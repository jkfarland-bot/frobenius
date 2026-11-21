module

/-
Run r25, seat L7: the compactness step for R-084 (upper half for every unit of the Dirichlet ring).

* `Dir.exists_of_local`: a family of "local" conditions on maps `ℕ → ℕ → M` (`M` finite and
  discrete), each satisfiable on every finite stage, is satisfiable at once (Tychonoff).
* `Dir.hasLevel_of_local`: if for every `N` some `g` gives `1 - f ∑ f^z E_p(g_z) ≡ 0 (mod p^k)`
  at every `n ≤ N`, then `f` has a level identity of level `L` in the Dirichlet ring, over any
  commutative ring `R` with `R / p^k R` finite (so `ℤ`, `ℤ_[p]`, `ℤ[χ]`, `𝓞_P`).
* `Dir.hasLevel_of_res`: the local conditions come from level identities of restrictions
  `res_q f` to `q`-smooth arguments, when every `n ≤ N` is `q`-smooth.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirTransfer

@[expose] public section

namespace FrobLevel

namespace Dir

open MvPowerSeries

section Agree

variable {M : Type*} [CommRing M]

/-- `a` and `b` agree at every argument `d ≤ N`. -/
def Agree (N : ℕ) (a b : ArithmeticFunction M) : Prop := ∀ d, d ≤ N → a d = b d

theorem Agree.refl' (N : ℕ) (a : ArithmeticFunction M) : Agree N a a := fun _ _ => rfl

theorem Agree.add {N : ℕ} {a b a' b' : ArithmeticFunction M} (h : Agree N a a')
    (h' : Agree N b b') : Agree N (a + b) (a' + b') := fun d hd => by
  rw [ArithmeticFunction.add_apply, ArithmeticFunction.add_apply, h d hd, h' d hd]

theorem Agree.sub {N : ℕ} {a b a' b' : ArithmeticFunction M} (h : Agree N a a')
    (h' : Agree N b b') : Agree N (a - b) (a' - b') := fun d hd => by
  rw [sub_apply', sub_apply', h d hd, h' d hd]

theorem Agree.mul {N : ℕ} {a b a' b' : ArithmeticFunction M} (h : Agree N a a')
    (h' : Agree N b b') : Agree N (a * b) (a' * b') := fun d hd => by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' := Nat.mem_divisorsAntidiagonal.mp hx
  have h1 : x.1 ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hx'.2) ⟨x.2, hx'.1.symm⟩
  have h2 : x.2 ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hx'.2) ⟨x.1, by rw [mul_comm]; exact hx'.1.symm⟩
  rw [h x.1 (h1.trans hd), h' x.2 (h2.trans hd)]

theorem Agree.pow {N : ℕ} {a a' : ArithmeticFunction M} (h : Agree N a a') (z : ℕ) :
    Agree N (a ^ z) (a' ^ z) := by
  induction z with
  | zero => simpa using Agree.refl' N (1 : ArithmeticFunction M)
  | succ z ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem Agree.sum {N : ℕ} {ι : Type*} (s : Finset ι) {a a' : ι → ArithmeticFunction M}
    (h : ∀ i ∈ s, Agree N (a i) (a' i)) : Agree N (∑ i ∈ s, a i) (∑ i ∈ s, a' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Agree.refl' N (0 : ArithmeticFunction M)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Agree.Ep (p : ℕ) [Fact p.Prime] {N : ℕ} {a a' : ArithmeticFunction M}
    (h : Agree N a a') : Agree N (Dir.Ep p a) (Dir.Ep p a') := fun d hd => by
  rw [Ep_apply, Ep_apply, frobPush_apply, frobPush_apply]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' := Nat.mem_divisors.mp hx
  have : x ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hx'.2) hx'.1
  rw [h x (this.trans hd)]

end Agree

section Compactness

variable {M : Type*} [CommRing M]

/-- A function `ℕ → M` as an arithmetic function (value `0` at `0`). -/
def toAF (v : ℕ → M) : ArithmeticFunction M := ⟨fun n => if n = 0 then 0 else v n, by simp⟩

theorem toAF_apply (v : ℕ → M) {n : ℕ} (hn : n ≠ 0) : toAF v n = v n := by
  show (if n = 0 then 0 else v n) = v n
  rw [if_neg hn]

/-- **Compactness.** `M` finite and discrete. If `Φ x n` depends only on the values `x z d` with
`z ≤ L` and `d ≤ n`, and every finite stage `∀ n ≤ N, Φ x n = 0` is solvable, then `Φ x = 0` is
solvable. -/
theorem exists_of_local [Finite M] [TopologicalSpace M] [DiscreteTopology M] (L : ℕ)
    (Φ : (ℕ → ℕ → M) → ArithmeticFunction M)
    (hloc : ∀ n x y, (∀ z ≤ L, ∀ d ≤ n, x z d = y z d) → Φ x n = Φ y n)
    (hfin : ∀ N, ∃ x, ∀ n ≤ N, Φ x n = 0) : ∃ x, Φ x = 0 := by
  classical
  have : CompactSpace M := Finite.compactSpace
  have hclosed : ∀ n, IsClosed {x : ℕ → ℕ → M | Φ x n = 0} := by
    intro n
    let pr : (ℕ → ℕ → M) → (Fin (L + 1) → Fin (n + 1) → M) := fun x z d => x z d
    let ex : (Fin (L + 1) → Fin (n + 1) → M) → (ℕ → ℕ → M) :=
      fun y z d => if h : z < L + 1 ∧ d < n + 1 then y ⟨z, h.1⟩ ⟨d, h.2⟩ else 0
    have hpr : Continuous pr := continuous_pi fun z => continuous_pi fun d =>
      (continuous_apply (d : ℕ)).comp (continuous_apply (z : ℕ))
    have heq : {x : ℕ → ℕ → M | Φ x n = 0} = pr ⁻¹' {y | Φ (ex y) n = 0} := by
      ext x
      show Φ x n = 0 ↔ Φ (ex (pr x)) n = 0
      rw [hloc n x (ex (pr x))]
      intro z hz d hd
      have hzd : z < L + 1 ∧ d < n + 1 := ⟨by omega, by omega⟩
      show x z d = (if h : z < L + 1 ∧ d < n + 1 then pr x ⟨z, h.1⟩ ⟨d, h.2⟩ else 0)
      rw [dif_pos hzd]
    rw [heq]
    exact (isClosed_discrete _).preimage hpr
  let t : ℕ → Set (ℕ → ℕ → M) := fun N => {x | ∀ n ≤ N, Φ x n = 0}
  have htcl : ∀ N, IsClosed (t N) := by
    intro N
    have : t N = ⋂ n ∈ Finset.range (N + 1), {x | Φ x n = 0} := by
      ext x; simp [t]
    rw [this]
    exact isClosed_biInter fun n _ => hclosed n
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    (fun N x hx n hn => hx n (hn.trans N.le_succ)) (fun N => hfin N) (htcl 0).isCompact htcl
  refine ⟨x, ArithmeticFunction.ext fun n => ?_⟩
  rw [ArithmeticFunction.zero_apply]
  exact (Set.mem_iInter.mp hx n) n le_rfl

end Compactness

section Transfer

/-- `mapHom φ` turns the level expression of `f` into that of `mapHom φ f`. -/
theorem mapHom_levelExpr {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℕ)
    [Fact p.Prime] (f : ArithmeticFunction R) (G : ℕ → ArithmeticFunction R) (L : ℕ) :
    mapHom φ (1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * Ep p (G z)) =
      1 - mapHom φ f * ∑ z ∈ Finset.range (L + 1), (mapHom φ f) ^ z * Ep p (mapHom φ (G z)) := by
  simp only [map_sub, map_one, map_mul, map_sum, map_pow, Ep_apply, mapHom_frobPush]

/-- **Local to global.** Let `φ : R → M` be a surjection onto a finite ring with kernel `p ^ k R`.
If for every `N` some `G` makes `1 - f ∑_{z ≤ L} f ^ z E_p(G_z)` divisible by `p ^ k` at every
argument `n ≤ N`, then `f` has a level `L` identity modulo `p ^ k` in the Dirichlet ring. -/
theorem hasLevel_of_local {R M : Type*} [CommRing R] [CommRing M] [Finite M] (p : ℕ)
    [hp : Fact p.Prime] {k L : ℕ} (φ : R →+* M) (hsurj : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 → (p : R) ^ k ∣ a) (hφp : φ ((p : R) ^ k) = 0)
    (f : ArithmeticFunction R)
    (hloc : ∀ N, ∃ G : ℕ → ArithmeticFunction R, ∀ n ≤ N,
      (p : R) ^ k ∣ (1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * Ep p (G z)) n) :
    HasLevel p (Ep p) f k L := by
  classical
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  set F := mapHom φ f with hF
  let Φ : (ℕ → ℕ → M) → ArithmeticFunction M := fun x =>
    1 - F * ∑ z ∈ Finset.range (L + 1), F ^ z * Ep p (toAF (x z))
  -- locality
  have hl : ∀ n x y, (∀ z ≤ L, ∀ d ≤ n, x z d = y z d) → Φ x n = Φ y n := by
    intro n x y hxy
    have hz : ∀ z ∈ Finset.range (L + 1), Agree n (F ^ z * Ep p (toAF (x z)))
        (F ^ z * Ep p (toAF (y z))) := by
      intro z hz
      have hz' : z ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hz)
      refine (Agree.refl' n _).mul (Agree.Ep p ?_)
      intro d hd
      rcases eq_or_ne d 0 with rfl | hd0
      · simp [toAF]
      · rw [toAF_apply _ hd0, toAF_apply _ hd0, hxy z hz' d hd]
    exact ((Agree.refl' n 1).sub ((Agree.refl' n F).mul (Agree.sum _ hz))) n le_rfl
  -- finite stages
  have hfin : ∀ N, ∃ x, ∀ n ≤ N, Φ x n = 0 := by
    intro N
    obtain ⟨G, hG⟩ := hloc N
    refine ⟨fun z d => φ (G z d), fun n hn => ?_⟩
    have hGz : ∀ z, mapHom φ (G z) = toAF (fun d => φ (G z d)) := by
      intro z; ext d
      rcases eq_or_ne d 0 with rfl | hd
      · simp [toAF]
      · rw [toAF_apply _ hd, mapHom_apply]
    have : Φ (fun z d => φ (G z d)) =
        mapHom φ (1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * Ep p (G z)) := by
      rw [mapHom_levelExpr]; simp only [Φ, hGz, hF]
    rw [this, mapHom_apply]
    obtain ⟨c, hc⟩ := hG n hn
    rw [hc, map_mul, hφp, zero_mul]
  obtain ⟨x, hx⟩ := exists_of_local L Φ hl hfin
  -- lift
  let s : M → R := fun c => (hsurj c).choose
  have hs : ∀ c, φ (s c) = c := fun c => (hsurj c).choose_spec
  let G' : ℕ → ArithmeticFunction R := fun z => toAF (fun d => s (x z d))
  have hG' : ∀ z, mapHom φ (G' z) = toAF (x z) := by
    intro z; ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [toAF]
    · rw [mapHom_apply, toAF_apply _ hd, toAF_apply _ hd, hs]
  have hmap : mapHom φ (1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * Ep p (G' z)) = 0 := by
    rw [mapHom_levelExpr]; simp only [hG', ← hF]; exact hx
  refine ⟨G', ?_⟩
  rw [← Nat.cast_pow]
  apply natCast_dvd_of_apply
  intro n
  rw [Nat.cast_pow]
  apply hker
  rw [← mapHom_apply, hmap, ArithmeticFunction.zero_apply]

/-- `(p : R[[x]]) ^ k ∣ a` gives `p ^ k ∣` every coefficient. -/
theorem coeff_dvd_of_dvd {R : Type*} [CommRing R] {n : ℕ} {c : R} {a : MvPowerSeries (Fin n) R}
    (h : (MvPowerSeries.C c) ∣ a) (e : Fin n →₀ ℕ) : c ∣ coeff e a := by
  obtain ⟨b, rfl⟩ := h
  rw [MvPowerSeries.coeff_C_mul]
  exact dvd_mul_right _ _

/-- **Local conditions from restrictions.** If for every `N` some finite family of primes `q`
covers every `m ≤ N` (each `0 < m ≤ N` is `q`-smooth) and the restriction `res_q f` has a level
`L` identity, then `f` has a level `L` identity in the Dirichlet ring. -/
theorem hasLevel_of_res {R M : Type*} [CommRing R] [CommRing M] [Finite M] (p : ℕ)
    [hp : Fact p.Prime] {k L : ℕ} (φ : R →+* M) (hsurj : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 → (p : R) ^ k ∣ a) (hφp : φ ((p : R) ^ k) = 0)
    (f : ArithmeticFunction R)
    (h : ∀ N, ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      (∀ m, m ≠ 0 → m ≤ N → ∃ e, smoothNum q e = m) ∧
        HasLevel p (frob p) (res hq hinj f) k L) :
    HasLevel p (Ep p) f k L := by
  apply hasLevel_of_local p φ hsurj hker hφp f
  intro N
  obtain ⟨n, q, hq, hinj, hsm, g, hg⟩ := h N
  refine ⟨fun z => iota hq hinj (g z), fun m hm => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [ArithmeticFunction.map_zero]; exact dvd_zero _
  obtain ⟨e, rfl⟩ := hsm m hm0 hm
  rw [← coeff_res hq hinj]
  have hres : res hq hinj (1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * Ep p (iota hq hinj (g z)))
      = 1 - res hq hinj f * ∑ z ∈ Finset.range (L + 1), (res hq hinj f) ^ z * frob p (g z) := by
    simp only [map_sub, map_one, map_mul, map_sum, map_pow, res_Ep, res_iota]
  rw [hres]
  apply coeff_dvd_of_dvd (c := (p : R) ^ k)
  have : (MvPowerSeries.C ((p : R) ^ k) : MvPowerSeries (Fin n) R) =
      (p : MvPowerSeries (Fin n) R) ^ k := by rw [map_pow, map_natCast]
  rw [this]; exact hg

end Transfer

end Dir

end FrobLevel
