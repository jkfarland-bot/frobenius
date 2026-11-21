module

/-
Run r25, seat L3: pure depth (note Corollary `cor:special` (c), ledger R-080/R-083) over `ℤ`, and
its Dirichlet-ring form, which settles note Corollary `cor:named` (b) at `p = 2`
(`d_2` and `μ * μ`, ledger R-084) over `ℤ`.

Setting: `u = σ(b) + p ^ J τ` (here `u = 1/f`).
* `exists_monic_depth` (any ring with a Frobenius lift): for every `m` a monic `P ∈ B[X]` of
  degree `m` with `p ^ (J m + v_p(m!)) ∣ P(u)` (scale the δ-tower of `τ` by `p ^ J`, shift by `σ b`).
* `depthMin p J k = min {m : J m + v_p(m!) ≥ k}`; `L_f + 1 ≤ depthMin` (`levelCount_le_depthMin`).
* `core_bound_depth`: L1's trace argument with the points `tw g u = σ b + p ^ J tw g τ`:
  a monic `P ∈ B[X]` of degree `p ^ n - 1` with `p ^ k ∣ P(u)` has
  `(p - 1)(k + n) < (p - 1) J (p ^ n - 1) + p ^ n`, when `τ` satisfies `(hu)`.
* `depth_le_of_monicAnn_int`: over `ℤ`, `τ` of full rank, `m < p ^ n`: `k ≤ J m + v_p(m!)`.
* `levelCount_depth_int`: `L_f + 1 = min(p ^ n, depthMin p J k)` in `ℤ[[x_1..x_n]]`.
* Dirichlet ring over `ℤ`: `levelCount_dir_depth_int` (infinitely many primes with `p ∤ τ(q)`:
  `L_f + 1 = depthMin p J k`), and `levelCount_d2_two`, `levelCount_moebius_mul_moebius_two`:
  at `p = 2`, `L + 1 = min {m : m + v_2(m!) ≥ k}`.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Lower
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirMain

@[expose] public section

namespace FrobLevel

/-! ## 1. The depth tower and the upper bound -/

section DepthTower

open Polynomial

variable {A : Type*} [CommRing A] [Nontrivial A]

/-- For `u = σ b + p ^ J τ` and every `m`: a monic `P ∈ B[X]` of degree `m` with
`p ^ (J m + v_p(m!)) ∣ P(u)`. -/
theorem exists_monic_depth {p : ℕ} [hp : Fact p.Prime] {σ : A →+* A} (h : IsFrobLift p σ)
    (J m : ℕ) {u b τ : A} (hu : u = σ b + (p : A) ^ J * τ) :
    ∃ P : A[X], P.Monic ∧ P.natDegree = m ∧ P ∈ BPoly σ ∧
      (p : A) ^ (J * m + padicValNat p m.factorial) ∣ P.eval u := by
  obtain ⟨P', hmon', hdeg', hB', hP'⟩ := exists_monic_tower h m τ
  set Q : A[X] := P'.scaleRoots ((p ^ J : ℕ) : A) with hQ
  set Y : A[X] := X - C (σ b) with hY
  have hYm : Y.Monic := monic_X_sub_C (σ b)
  have hYd : Y.natDegree = 1 := natDegree_X_sub_C (σ b)
  have hQm : Q.Monic := (monic_scaleRoots_iff _).2 hmon'
  have hQd : Q.natDegree = m := by rw [hQ, natDegree_scaleRoots, hdeg']
  refine ⟨Q.comp Y, hQm.comp hYm (by rw [hYd]; exact one_ne_zero), ?_, ?_, ?_⟩
  · rw [natDegree_comp_eq_of_mul_ne_zero (by rw [hQm.leadingCoeff, hYm.leadingCoeff]; simp),
      hQd, hYd, mul_one]
  · exact comp_mem_BPoly (scaleRoots_mem_BPoly hB' _) (sub_mem (X_mem_BPoly σ) (C_mem_BPoly σ b))
  · have hYu : Y.eval u = ((p ^ J : ℕ) : A) * τ := by
      rw [hY, eval_sub, eval_X, eval_C, hu, Nat.cast_pow]; ring
    have hev : (Q.comp Y).eval u = ((p : A) ^ J) ^ m * P'.eval τ := by
      rw [eval_comp, hYu, hQ]
      have := scaleRoots_eval₂_mul (p := P') (RingHom.id A) τ ((p ^ J : ℕ) : A)
      simp only [eval₂_id, RingHom.id_apply] at this
      rw [this, hdeg', Nat.cast_pow]
    rw [hev, ← pow_mul, pow_add]
    exact mul_dvd_mul_left _ hP'

end DepthTower

section DepthMin

variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_depth (J k : ℕ) : ∃ m, k ≤ J * m + padicValNat p m.factorial :=
  ⟨kempner p k, le_add_left (kempner_spec p k)⟩

/-- `min {m : J m + v_p(m!) ≥ k}`; for `J = 0` this is `S(p ^ k)`. -/
noncomputable def depthMin (J k : ℕ) : ℕ := Nat.find (exists_depth p J k)

theorem depthMin_spec (J k : ℕ) : k ≤ J * depthMin p J k + padicValNat p (depthMin p J k).factorial :=
  Nat.find_spec (exists_depth p J k)

theorem depthMin_le {J k m : ℕ} (h : k ≤ J * m + padicValNat p m.factorial) : depthMin p J k ≤ m :=
  Nat.find_min' (exists_depth p J k) h

theorem depthMin_pos {J k : ℕ} (hk : 1 ≤ k) : 1 ≤ depthMin p J k := by
  by_contra h0
  have h := depthMin_spec p J k
  rw [show depthMin p J k = 0 by omega] at h
  simp at h
  omega

theorem depthMin_le_kempner (J k : ℕ) : depthMin p J k ≤ kempner p k :=
  depthMin_le p (le_add_left (kempner_spec p k))

/-- **Upper bound, pure depth** (any ring with a Frobenius lift): if `f u = 1` and
`u = σ b + p ^ J τ`, then there is a level identity at `depthMin - 1`. -/
theorem hasLevel_depth {A : Type*} [CommRing A] [Nontrivial A] {σ : A →+* A}
    (h : IsFrobLift p σ) {f u b τ : A} (hfu : f * u = 1) {J : ℕ}
    (hub : u = σ b + (p : A) ^ J * τ) {k : ℕ} (hk : 1 ≤ k) :
    HasLevel p σ f k (depthMin p J k - 1) := by
  obtain ⟨P, hm, hd, hB, hP⟩ := exists_monic_depth h J (depthMin p J k) hub
  have e : depthMin p J k - 1 + 1 = depthMin p J k := Nat.sub_add_cancel (depthMin_pos p hk)
  apply MonicAnn.hasLevel (u := u) (by rw [hfu, sub_self]; exact dvd_zero _)
  rw [e]
  exact ⟨P, hm, hd, hB, (pow_dvd_pow _ (depthMin_spec p J k)).trans hP⟩

theorem levelCount_le_depthMin {A : Type*} [CommRing A] [Nontrivial A] {σ : A →+* A}
    (h : IsFrobLift p σ) {f u b τ : A} (hfu : f * u = 1) {J : ℕ}
    (hub : u = σ b + (p : A) ^ J * τ) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p σ f k + 1 ≤ depthMin p J k := by
  have h1 := levelCount_le (hasLevel_depth p h hfu hub hk)
  have h2 := depthMin_pos p (J := J) hk
  omega

end DepthMin

/-! ## 2. The trace argument with depth -/

section CoreDepth

open MvPowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] {n p : ℕ}

/-- The core bound with depth: `u = σ b + p ^ J τ`, `τ` satisfying `(hu)`. -/
theorem core_bound_depth [hp : Fact p.Prime] {ζ : O} (hζ : IsPrimitiveRoot ζ p)
    (hπ : Prime (ζ - 1)) (hpπ : Associated ((ζ - 1) ^ (p - 1)) (p : O)) (J : ℕ)
    (b τ : MvPowerSeries (Fin n) O)
    (hτ : ∀ h : Fin n → Fin p, h ≠ 0 →
      ∃ m : Fin n →₀ ℕ, ¬ p ∣ ∑ i, (h i : ℕ) * m i ∧ ¬ (ζ - 1) ∣ coeff m τ)
    {P : Polynomial (MvPowerSeries (Fin n) O)} (hmon : P.Monic) (hdeg : P.natDegree + 1 = p ^ n)
    (hB : P ∈ BPoly (frob p)) {k : ℕ}
    (hk : (p : MvPowerSeries (Fin n) O) ^ k ∣ P.eval (frob p b + C ((p : O) ^ J) * τ)) :
    (p - 1) * (k + n) < (p - 1) * (J * (p ^ n - 1)) + p ^ n := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : IsDomain (MvPowerSeries (Fin n) O) := NoZeroDivisors.to_isDomain _
  have : (Ideal.span {ζ - 1} : Ideal O).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have : IsDomain (O ⧸ (Ideal.span {ζ - 1} : Ideal O)) := Ideal.Quotient.isDomain _
  have : IsDomain (MvPowerSeries (Fin n) (O ⧸ (Ideal.span {ζ - 1} : Ideal O))) :=
    NoZeroDivisors.to_isDomain _
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hp2 := hp.out.two_le
  have hπp : (ζ - 1) ∣ (p : O) := (dvd_pow_self (ζ - 1) (by omega)).trans hpπ.dvd
  have hp0 : (p : O) ≠ 0 := (hpπ.ne_zero_iff).1 (pow_ne_zero _ hπ.ne_zero)
  set u := frob p b + C ((p : O) ^ J) * τ with hu
  set κ : MvPowerSeries (Fin n) O := C ((p : O) ^ J * (ζ - 1)) with hκ
  have hκ0 : κ ≠ 0 := constantCoeff_C_ne (mul_ne_zero (pow_ne_zero _ hp0) hπ.ne_zero)
  choose E hEeq hEne using fun h : Fin n → Fin p => exists_E hπ hπp τ h
  have hEne' : ∀ h : Fin n → Fin p, h ≠ 0 → resPi ζ (E h) ≠ 0 := fun h hh => by
    obtain ⟨m, hm1, hm2⟩ := hτ h hh
    exact hEne h m hm1 hm2
  have huE : ∀ h, u - tw ζ h u = κ * E h := fun h => by
    rw [hu, map_add, map_mul, tw_C, tw_frob hζp, hκ, map_mul]
    have := hEeq h
    linear_combination (C ((p : O) ^ J)) * this
  set N := p ^ n with hN
  have hcard : Fintype.card (Fin n → Fin p) = N := by simp [hN]
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ hp.out.pos
  set D' := ∏ h ∈ Finset.univ.erase (0 : Fin n → Fin p), E h with hD'
  set z : (Fin n → Fin p) → MvPowerSeries (Fin n) O := fun g => tw ζ g u with hz
  have hzdiff : ∀ g h, z g - z (g + h) = κ * tw ζ g (E h) := by
    intro g h
    simp only [hz]
    rw [← tw_tw hζp, ← map_sub, huE, map_mul, hκ, tw_C]
  have hzinj : Function.Injective z := by
    intro g g' hgg'
    by_contra hne
    have h0 : g' - g ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have := hzdiff g (g' - g)
    rw [show g + (g' - g) = g' by abel, hgg', sub_self] at this
    have h1 : tw ζ g (E (g' - g)) = 0 := (mul_eq_zero.1 this.symm).resolve_left hκ0
    have h2 : E (g' - g) = 0 := by
      have := congrArg (tw ζ (-g)) h1
      rwa [tw_tw hζp, neg_add_cancel, tw_zero, map_zero] at this
    exact hEne' _ h0 (by rw [h2, map_zero])
  have hD : ∀ g, ∏ h ∈ Finset.univ.erase g, (z g - z h) = κ ^ (N - 1) * tw ζ g D' := by
    intro g
    rw [prod_erase_translate (fun h => z g - z h) g, Finset.prod_congr rfl fun h _ => hzdiff g h,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hcard, hD', map_prod]
  set c := ∏ h ∈ Finset.univ.erase (0 : Fin n → Fin p), tw ζ h D' with hcdef
  have hc : ∀ g : Fin n → Fin p, ∏ g' ∈ Finset.univ.erase g, tw ζ g' D' = tw ζ g c := by
    intro g
    rw [prod_erase_translate (fun g' => tw ζ g' D') g, hcdef, map_prod]
    exact Finset.prod_congr rfl fun h _ => (tw_tw hζp g h D').symm
  obtain ⟨y, hy⟩ := hk
  have hQz : ∀ g, P.eval (z g) = (p : MvPowerSeries (Fin n) O) ^ k * tw ζ g y := fun g => by
    simp only [hz]
    rw [eval_tw hζp hB, hy, map_mul, map_pow, map_natCast]
  have hL := lagrange_cleared z hzinj P hmon (by rw [hdeg, hcard])
  simp only [hD, hQz] at hL
  have hLHS : ∏ g : Fin n → Fin p, (κ ^ (N - 1) * tw ζ g D')
      = κ ^ ((N - 1) * N) * ∏ g : Fin n → Fin p, tw ζ g D' := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, ← pow_mul]
  have hRHS : ∀ g : Fin n → Fin p, (p : MvPowerSeries (Fin n) O) ^ k * tw ζ g y *
      ∏ g' ∈ Finset.univ.erase g, (κ ^ (N - 1) * tw ζ g' D')
      = κ ^ ((N - 1) * (N - 1)) * ((p : MvPowerSeries (Fin n) O) ^ k * tw ζ g (y * c)) := by
    intro g
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hcard, ← pow_mul, hc g, map_mul]
    ring
  obtain ⟨s, hs⟩ := natCast_pow_dvd_sum_tw hζ (y * c)
  rw [hLHS, Finset.sum_congr rfl (fun g _ => hRHS g), ← Finset.mul_sum, ← Finset.mul_sum, hs] at hL
  have hsplit : (N - 1) * N = (N - 1) * (N - 1) + (N - 1) := by
    obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [hM, Nat.add_sub_cancel]; ring
  rw [hsplit, pow_add, mul_assoc] at hL
  have hL2 := mul_left_cancel₀ (pow_ne_zero _ hκ0) hL
  -- `p = π ^ (p - 1) v`
  obtain ⟨v, hv⟩ := hpπ
  set Cπ : MvPowerSeries (Fin n) O := C (ζ - 1) with hCπdef
  have hCπ : Cπ ≠ 0 := constantCoeff_C_ne hπ.ne_zero
  have hpA : (p : MvPowerSeries (Fin n) O) = Cπ ^ (p - 1) * C (v : O) := by
    rw [hCπdef, ← map_pow, ← map_mul, hv, map_natCast]
  have hκA : κ = Cπ ^ ((p - 1) * J + 1) * C (v : O) ^ J := by
    rw [hκ, map_mul, map_pow, map_natCast, hpA, hCπdef]; ring
  by_contra hge
  push Not at hge
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hge
  set M := (p - 1) * J * (N - 1) + (N - 1) with hM
  have hX : Cπ ^ M * (C (v : O) ^ (J * (N - 1)) * ∏ g : Fin n → Fin p, tw ζ g D')
      = Cπ ^ M * (Cπ * (Cπ ^ t * (C (v : O) ^ (k + n) * s))) := by
    have e1 : κ ^ (N - 1) = Cπ ^ M * C (v : O) ^ (J * (N - 1)) := by
      rw [hκA, mul_pow, ← pow_mul, ← pow_mul, hM]
      congr 1; congr 1; ring
    have e2 : (p : MvPowerSeries (Fin n) O) ^ k * ((p : MvPowerSeries (Fin n) O) ^ n * s)
        = Cπ ^ M * (Cπ * (Cπ ^ t * (C (v : O) ^ (k + n) * s))) := by
      rw [show (p : MvPowerSeries (Fin n) O) ^ k * ((p : MvPowerSeries (Fin n) O) ^ n * s)
          = (p : MvPowerSeries (Fin n) O) ^ (k + n) * s by ring, hpA, mul_pow, ← pow_mul]
      have e3 : (p - 1) * (k + n) = M + 1 + t := by
        rw [hM]
        have : (p - 1) * (J * (N - 1)) = (p - 1) * J * (N - 1) := by ring
        omega
      rw [e3, pow_add, pow_add]
      ring
    rw [← e2, ← hL2, e1]
    ring
  have hX2 := mul_left_cancel₀ (pow_ne_zero _ hCπ) hX
  have h0 := congrArg (resPi ζ) hX2
  rw [map_mul, map_mul, hCπdef, resPi_C_pi, zero_mul, map_prod] at h0
  simp only [resPi_tw] at h0
  rw [Finset.prod_const, hD', map_prod] at h0
  have hvu : IsUnit (resPi ζ (C (v : O) ^ (J * (N - 1)) : MvPowerSeries (Fin n) O)) :=
    ((Units.isUnit v).map (C (σ := Fin n) (R := O))).pow _ |>.map (resPi ζ)
  refine pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun h hh => hEne' h ?_)
    ((hvu.mul_right_eq_zero).1 h0)
  exact (Finset.mem_erase.1 hh).1

end CoreDepth

/-! ## 3. The lower bound over `ℤ` and the exact count in power series -/

section DepthInt

open MvPowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

open NumberField in
/-- Lower bound, pure depth, over `ℤ`: for `u = σ b + p ^ J τ` with `τ` of full rank, a monic
annihilator of `u` modulo `p ^ k` of degree `m < p ^ n` has `k ≤ J m + v_p(m!)`. -/
theorem depth_le_of_monicAnn_int {n k m J : ℕ} {u b τ : MvPowerSeries (Fin n) ℤ}
    (hub : u = frob p b + (p : MvPowerSeries (Fin n) ℤ) ^ J * τ) (hτ : FullRank p τ)
    (hm : m < p ^ n) (hP : MonicAnn p (frob p) u k m) : k ≤ J * m + padicValNat p m.factorial := by
  classical
  obtain ⟨P, hmon, hdeg, hB, hPu⟩ := hP
  set d := p ^ n - 1 - m with hd
  obtain ⟨Q, hQm, hQd, hQB, hQu⟩ :=
    exists_monic_depth (frob_isFrobLift p (int_pow_sub p)) J d hub
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p : ℚ) := ⟨by exact_mod_cast hp.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hζK : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)) p :=
    IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hζ : IsPrimitiveRoot hζK.toInteger p := hζK.toInteger_isPrimitiveRoot
  have hπ : Prime (hζK.toInteger - 1) := hζK.zeta_sub_one_prime'
  have hpπ : Associated ((hζK.toInteger - 1) ^ (p - 1)) (p : 𝓞 (CyclotomicField p ℚ)) :=
    IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζK
  have hπp : (hζK.toInteger - 1) ∣ (p : 𝓞 (CyclotomicField p ℚ)) :=
    (dvd_pow_self _ (by have := hp.out.two_le; omega)).trans hpπ.dvd
  set O := 𝓞 (CyclotomicField p ℚ)
  set φ : MvPowerSeries (Fin n) ℤ →+* MvPowerSeries (Fin n) O :=
    MvPowerSeries.map (Int.castRingHom O) with hφ
  have hfφ : ∀ a, φ (frob p a) = frob p (φ a) := fun a => by
    simp [hφ, frob_apply, MvPowerSeries.map_expand]
  have hRm : ((P * Q).map φ).Monic := (hmon.mul hQm).map φ
  have hRd : ((P * Q).map φ).natDegree + 1 = p ^ n := by
    rw [(hmon.mul hQm).natDegree_map, hmon.natDegree_mul hQm, hdeg, hQd, hd]
    have := Nat.one_le_pow n p hp.out.pos
    omega
  have hRB : (P * Q).map φ ∈ BPoly (frob p) := by
    rw [mem_BPoly_iff]
    intro i
    rw [Polynomial.coeff_map]
    obtain ⟨a, ha⟩ := mem_BPoly_iff.1 (mul_mem hB hQB) i
    exact ⟨φ a, by rw [← ha, hfφ]⟩
  have hφu : φ u = frob p (φ b) + C ((p : O) ^ J) * φ τ := by
    rw [hub, map_add, map_mul, map_pow, map_natCast, hfφ, ← map_natCast (C (σ := Fin n) (R := O)),
      map_pow]
  have hRu : (p : MvPowerSeries (Fin n) O) ^ (k + (J * d + padicValNat p d.factorial))
      ∣ ((P * Q).map φ).eval (frob p (φ b) + C ((p : O) ^ J) * φ τ) := by
    rw [← hφu, Polynomial.eval_map, Polynomial.eval₂_hom, Polynomial.eval_mul, pow_add]
    have := mul_dvd_mul hPu hQu
    obtain ⟨w, hw⟩ := this
    exact ⟨φ w, by rw [hw]; simp only [map_mul, map_pow, map_natCast]⟩
  have hcore := core_bound_depth hζ hπ hpπ J (φ b) (φ τ)
    (fun h hh => hu_of_fullRank p hπ hπp hτ h hh) hRm hRd hRB hRu
  have hleg := legendre_split p n m d (by rw [hd]; have := Nat.one_le_pow n p hp.out.pos; omega)
  have hmd : p ^ n - 1 = m + d := by rw [hd]; have := Nat.one_le_pow n p hp.out.pos; omega
  rw [hmd] at hcore
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  set vm := padicValNat p m.factorial
  set vd := padicValNat p d.factorial
  have e1 : (p - 1) * (J * (m + d)) = (p - 1) * (J * m) + (p - 1) * (J * d) := by ring
  have e2 : (p - 1) * (k + (J * d + vd) + n)
      = (p - 1) * (k + n) + (p - 1) * (J * d) + (p - 1) * vd := by ring
  have hcore' : (p - 1) * (k + (J * d + vd) + n) < (p - 1) * (J * m + J * d + vm + vd + n) + 1 := by
    have e3 : (p - 1) * (J * m + J * d + vm + vd + n)
        = (p - 1) * (J * m) + (p - 1) * (J * d) + ((p - 1) * (vm + vd) + n * (p - 1)) := by ring
    rw [e2, e3]
    have e4 : (p - 1) * (k + (J * d + vd) + n) = (p - 1) * (k + n + J * d + vd) := by ring
    omega
  have h1 : (p - 1) * (k + (J * d + vd) + n) ≤ (p - 1) * (J * m + J * d + vm + vd + n) := by
    omega
  have := Nat.le_of_mul_le_mul_left h1 hp1
  omega

/-- **Pure depth, exact** (note Corollary `cor:special` (c) with `ρ(τ) = n = r_f`), over `ℤ`:
`f u = 1`, `u = σ b + p ^ J τ`, `τ` of full rank, `k ≥ 1`:
`L_f(p, k) + 1 = min(p ^ n, min {m : J m + v_p(m!) ≥ k})`. -/
theorem levelCount_depth_int {n J : ℕ} {f u b τ : MvPowerSeries (Fin n) ℤ} (hfu : f * u = 1)
    (hub : u = frob p b + (p : MvPowerSeries (Fin n) ℤ) ^ J * τ) (hτ : FullRank p τ) {k : ℕ}
    (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1 = min (p ^ n) (depthMin p J k) := by
  have hup1 := levelCount_le_min p (int_pow_sub p)
    ⟨⟨f, u, hfu, by rw [mul_comm]; exact hfu⟩, rfl⟩ hk
  have hup2 := levelCount_le_depthMin p (frob_isFrobLift p (int_pow_sub p)) hfu hub hk
  refine le_antisymm (le_min (hup1.trans (min_le_left _ _)) hup2) ?_
  have hfu' : (p : MvPowerSeries (Fin n) ℤ) ^ k ∣ f * u - 1 := by
    rw [hfu, sub_self]; exact dvd_zero _
  have hpk := not_isUnit_pow_mvPowerSeries (τ := Fin n) p (int_not_isUnit p) hk
  have hex := monicAnn_kempner (frob_isFrobLift p (int_pow_sub p)) u k
  rw [levelCount_add_one hfu' hpk hex]
  have hmin := monicAnn_annDegree hex
  by_cases hlt : annDegree p (frob p) u k < p ^ n
  · exact (min_le_right _ _).trans (depthMin_le p (depth_le_of_monicAnn_int p hub hτ hlt hmin))
  · exact (min_le_left _ _).trans (not_lt.1 hlt)

end DepthInt

/-! ## 4. The Dirichlet ring over `ℤ` -/

namespace Dir

section DirDepth

open MvPowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Pure depth in the Dirichlet ring over `ℤ`.** If `f u = 1`, `u = E_p b + p ^ J τ`, and
infinitely many primes `q` have `p ∤ τ(q)`, then `L_f(p, k) + 1 = min {m : J m + v_p(m!) ≥ k}`. -/
theorem levelCount_dir_depth_int {f u b τ : ArithmeticFunction ℤ} (hfu : f * u = 1) {J : ℕ}
    (hub : u = Ep p b + (p : ArithmeticFunction ℤ) ^ J * τ)
    (hinf : {q : ℕ | q.Prime ∧ ¬ (p : ℤ) ∣ τ q}.Infinite) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 = depthMin p J k := by
  have hup := levelCount_le_depthMin p (ep_isFrobLift p (int_pow_sub p)) hfu hub hk
  obtain ⟨q, hinj, hqS⟩ := exists_injective_of_infinite hinf (p * k)
  have hq : ∀ i, (q i).Prime := fun i => (hqS i).1
  have hex := hasLevel_depth p (ep_isFrobLift p (int_pow_sub p)) hfu hub hk
  have hle := levelCount_map_le (res hq hinj) (σ := Ep p) (σ' := frob p)
    (fun a => res_Ep hq hinj p a) hex
  have hub' : res hq hinj u = frob p (res hq hinj b) +
      (p : MvPowerSeries (Fin (p * k)) ℤ) ^ J * res hq hinj τ := by
    rw [hub, map_add, map_mul, map_pow, map_natCast, res_Ep]
  have heq := levelCount_depth_int p (by rw [← map_mul, hfu, map_one]) hub'
    (fullRank_res hq hinj τ (fun i => (hqS i).2)) hk
  have hcap : depthMin p J k ≤ p ^ (p * k) :=
    (depthMin_le_kempner p J k).trans (kempner_le_pow_mul p k)
  rw [min_eq_right hcap] at heq
  omega

/-- `E_p b` vanishes at a prime (a prime is not a `p`-th power). -/
theorem Ep_apply_prime {q : ℕ} (hq : q.Prime) (b : ArithmeticFunction ℤ) : Ep p b q = 0 := by
  rw [Ep_apply, frobPush_apply_of_not]
  rintro ⟨j, hj⟩
  exact hp.out.one_lt.ne' (hq.pow_eq_iff.1 hj).2

/-- A Frobenius-lift decomposition `u = E_p b + p τ` in the Dirichlet ring over `ℤ`, with
`p τ(q) = u(q)` at every prime `q`. -/
theorem exists_decomp (u : ArithmeticFunction ℤ) :
    ∃ τ : ArithmeticFunction ℤ, u ^ p = Ep p u + (p : ArithmeticFunction ℤ) ^ 1 * τ := by
  obtain ⟨d, hd⟩ := ep_isFrobLift p (int_pow_sub p) u
  exact ⟨-d, by rw [pow_one, mul_neg, ← hd]; ring⟩

/-- **Note Corollary `cor:named` (b) at `p = 2`, `d_2 = ζ * ζ`, over `ℤ`:**
`L_(d_2)(2, k) + 1 = min {m : m + v_2(m!) ≥ k}` for every `k ≥ 1`. -/
theorem levelCount_d2_two {k : ℕ} (hk : 1 ≤ k) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    levelCount 2 (Ep 2) (zetaZ * zetaZ) k + 1 = depthMin 2 1 k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `u = μ * μ = μ ^ 2 = E_2 μ + 2 τ`
  obtain ⟨τ, hτ⟩ := exists_decomp 2 ArithmeticFunction.moebius
  have hfu : zetaZ * zetaZ * (ArithmeticFunction.moebius * ArithmeticFunction.moebius) = 1 := by
    have h1 : zetaZ * ArithmeticFunction.moebius = 1 := by
      rw [zetaZ, ArithmeticFunction.coe_zeta_mul_moebius]
    calc zetaZ * zetaZ * (ArithmeticFunction.moebius * ArithmeticFunction.moebius)
        = (zetaZ * ArithmeticFunction.moebius) * (zetaZ * ArithmeticFunction.moebius) := by ring
      _ = 1 := by rw [h1, one_mul]
  refine levelCount_dir_depth_int 2 hfu (b := ArithmeticFunction.moebius) (τ := τ) (J := 1)
    (by rw [← hτ, sq]) ?_ hk
  refine Nat.infinite_setOfPred_prime.mono fun q hq => ⟨hq, ?_⟩
  -- `2 τ(q) = (μ * μ)(q) - E_2 μ (q) = -2`
  have hval : (2 : ℤ) * τ q = -2 := by
    have := congrArg (fun F : ArithmeticFunction ℤ => F q) hτ
    rw [ArithmeticFunction.add_apply, pow_one, natCast_mul_apply, Ep_apply_prime 2 hq, zero_add,
      sq, mul_apply_prime _ _ hq, ArithmeticFunction.moebius_apply_prime hq] at this
    simp at this
    push_cast at this
    linarith
  have : τ q = -1 := by linarith
  rw [this]
  exact not_dvd_of_natAbs_one 2 rfl

/-- **Note Corollary `cor:named` (b) at `p = 2`, `d_2⁻¹ = μ * μ`, over `ℤ`.** -/
theorem levelCount_moebius_mul_moebius_two {k : ℕ} (hk : 1 ≤ k) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    levelCount 2 (Ep 2) (ArithmeticFunction.moebius * ArithmeticFunction.moebius) k + 1 =
      depthMin 2 1 k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ⟩ := exists_decomp 2 zetaZ
  have hfu : ArithmeticFunction.moebius * ArithmeticFunction.moebius * (zetaZ * zetaZ) = 1 := by
    have h1 : zetaZ * ArithmeticFunction.moebius = 1 := by
      rw [zetaZ, ArithmeticFunction.coe_zeta_mul_moebius]
    calc ArithmeticFunction.moebius * ArithmeticFunction.moebius * (zetaZ * zetaZ)
        = (zetaZ * ArithmeticFunction.moebius) * (zetaZ * ArithmeticFunction.moebius) := by ring
      _ = 1 := by rw [h1, one_mul]
  refine levelCount_dir_depth_int 2 hfu (b := zetaZ) (τ := τ) (J := 1) (by rw [← hτ, sq]) ?_ hk
  refine Nat.infinite_setOfPred_prime.mono fun q hq => ⟨hq, ?_⟩
  have hval : (2 : ℤ) * τ q = 2 := by
    have := congrArg (fun F : ArithmeticFunction ℤ => F q) hτ
    rw [ArithmeticFunction.add_apply, pow_one, natCast_mul_apply, Ep_apply_prime 2 hq, zero_add,
      sq, mul_apply_prime _ _ hq, zetaZ_apply one_ne_zero, zetaZ_apply hq.ne_zero] at this
    push_cast at this
    linarith
  have : τ q = 1 := by linarith
  rw [this]
  exact not_dvd_of_natAbs_one 2 rfl

end DirDepth

end Dir

end FrobLevel
