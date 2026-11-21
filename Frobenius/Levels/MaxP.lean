module

/-
Run r25, seat L9: note Proposition `prop:maxP` (R-084) in Chinese-remainder form, for the
Dirichlet ring over any commutative ring `R`.

* `HasLevelIdeal p f I L`: a level-`L` identity `1 - f ∑_{z ≤ L} f^z E_p(g_z)` with all values in
  the ideal `I` of `R`; `levelCountIdeal` its least `L`.
* `hasLevel_iff_ideal`: for `I = p^k R` this is the level identity modulo `p^k` (`HasLevel`).
* `hasLevelIdeal_biInf_iff`: for pairwise coprime ideals `I_i` (`i ∈ s`), a level-`L` identity
  modulo `⨅ I_i` exists iff one exists modulo every `I_i`.
* `levelCount_eq_sup_ideal` (**Prop maxP, CRT form**): if `p^k R = ⨅_{i ∈ s} I_i` with the
  `I_i` pairwise coprime and `f(1)` a unit, then `L_f(p, k) = max_i levelCountIdeal p f I_i`.

For `R = ℤ[χ]` and `I_P = P^(e k)` (the primes `P` above `p`, ramification `e`) the hypothesis is
the factorization `p^k R = ∏ P^(e k) = ⨅ P^(e k)`. Not formalized here: the identification of
the count modulo `P^(e k)` with the count over the completion `𝓞_P` modulo `p^k` (the note's
`L_{f,P}`), and the factorization itself for a given `χ`.

Lean v4.33.1 with Mathlib. No sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirMain
public import Frobenius.Levels.A1Gen

@[expose] public section

namespace FrobLevel

namespace Dir

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- The level expression `1 - f ∑_{z ≤ L} f^z E_p(g_z)`. -/
noncomputable def levelExpr {S : Type*} [CommRing S] (f : ArithmeticFunction S)
    (g : ℕ → ArithmeticFunction S) (L : ℕ) : ArithmeticFunction S :=
  1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * Ep p (g z)

/-- A level-`L` identity modulo the ideal `I` (pointwise). -/
def HasLevelIdeal (f : ArithmeticFunction R) (I : Ideal R) (L : ℕ) : Prop :=
  ∃ g : ℕ → ArithmeticFunction R, ∀ n, levelExpr p f g L n ∈ I

/-- The least level modulo `I`. -/
noncomputable def levelCountIdeal (f : ArithmeticFunction R) (I : Ideal R) : ℕ :=
  sInf {L | HasLevelIdeal p f I L}

theorem hasLevel_iff_ideal (f : ArithmeticFunction R) (k L : ℕ) :
    HasLevel p (Ep p) f k L ↔ HasLevelIdeal p f (Ideal.span {(p : R) ^ k}) L := by
  constructor
  · rintro ⟨g, c, hc⟩
    refine ⟨g, fun n => Ideal.mem_span_singleton.2 ⟨c n, ?_⟩⟩
    have := congrArg (fun F : ArithmeticFunction R => F n) hc
    rw [levelExpr, this, ← Nat.cast_pow, natCast_mul_apply]; push_cast; ring
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [← Nat.cast_pow]
    apply natCast_dvd_of_apply
    intro n
    have := Ideal.mem_span_singleton.1 (hg n)
    push_cast
    exact this

theorem levelCount_eq_ideal (f : ArithmeticFunction R) (k : ℕ) :
    levelCount p (Ep p) f k = levelCountIdeal p f (Ideal.span {(p : R) ^ k}) := by
  simp only [levelCount, levelCountIdeal, hasLevel_iff_ideal]

theorem HasLevelIdeal.mono_ideal {f : ArithmeticFunction R} {I J : Ideal R} {L : ℕ}
    (h : HasLevelIdeal p f I L) (hIJ : I ≤ J) : HasLevelIdeal p f J L := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun n => hIJ (hg n)⟩

theorem HasLevelIdeal.mono {f : ArithmeticFunction R} {I : Ideal R} {L L' : ℕ}
    (h : HasLevelIdeal p f I L) (hL : L ≤ L') : HasLevelIdeal p f I L' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨fun z => if z < L + 1 then g z else 0, fun n => ?_⟩
  have hs : ∑ z ∈ Finset.range (L' + 1), f ^ z * Ep p (if z < L + 1 then g z else 0)
      = ∑ z ∈ Finset.range (L + 1), f ^ z * Ep p (g z) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show L + 1 ≤ L' + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (L + 1) (L' + 1)) (fun z hz => by
      rw [Finset.mem_Ico] at hz
      rw [if_neg (by omega), map_zero, mul_zero]), add_zero]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Finset.mem_range] at hz
    rw [if_pos hz]
  have := hg n
  rwa [levelExpr, ← hs] at this

/-- Reduction modulo `I` commutes with the level expression. -/
theorem mapHom_levelExpr' {S : Type*} [CommRing S] (φ : R →+* S) (f : ArithmeticFunction R)
    (g : ℕ → ArithmeticFunction R) (L : ℕ) :
    mapHom φ (levelExpr p f g L) = levelExpr p (mapHom φ f) (fun z => mapHom φ (g z)) L := by
  simp only [levelExpr, map_sub, map_one, map_mul, map_sum, map_pow]
  congr 2
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  exact mapHom_frobPush φ p (g z)

theorem mem_iff_mapHom (I : Ideal R) (F : ArithmeticFunction R) :
    (∀ n, F n ∈ I) ↔ mapHom (Ideal.Quotient.mk I) F = 0 := by
  constructor
  · intro h; ext n; rw [mapHom_apply]; exact Ideal.Quotient.eq_zero_iff_mem.2 (h n)
  · intro h n
    have := congrArg (fun G : ArithmeticFunction (R ⧸ I) => G n) h
    simp only [mapHom_apply, ArithmeticFunction.zero_apply] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this

/-- **Chinese remainder step**: for coprime `I`, `J`, a level-`L` identity modulo `I ⊓ J` exists
iff one exists modulo `I` and one modulo `J`. -/
theorem hasLevelIdeal_inf_iff {f : ArithmeticFunction R} {I J : Ideal R} (hIJ : I ⊔ J = ⊤)
    {L : ℕ} : HasLevelIdeal p f (I ⊓ J) L ↔ HasLevelIdeal p f I L ∧ HasLevelIdeal p f J L := by
  constructor
  · intro h; exact ⟨h.mono_ideal p inf_le_left, h.mono_ideal p inf_le_right⟩
  rintro ⟨⟨g1, h1⟩, ⟨g2, h2⟩⟩
  have h1' : (1 : R) ∈ I ⊔ J := by rw [hIJ]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1'
  -- `h = b g1 + a g2`: `≡ g1` modulo `I`, `≡ g2` modulo `J`
  set h : ℕ → ArithmeticFunction R := fun z => ⟨fun n => b * g1 z n + a * g2 z n, by simp⟩ with hh
  have keyI : ∀ z, mapHom (Ideal.Quotient.mk I) (h z) = mapHom (Ideal.Quotient.mk I) (g1 z) := by
    intro z; ext n
    rw [mapHom_apply, mapHom_apply, hh]
    show Ideal.Quotient.mk I (b * g1 z n + a * g2 z n) = _
    simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul, add_zero]
    have : Ideal.Quotient.mk I b = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha,
        zero_add]
    rw [this, one_mul]
  have keyJ : ∀ z, mapHom (Ideal.Quotient.mk J) (h z) = mapHom (Ideal.Quotient.mk J) (g2 z) := by
    intro z; ext n
    rw [mapHom_apply, mapHom_apply, hh]
    show Ideal.Quotient.mk J (b * g1 z n + a * g2 z n) = _
    simp only [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul, zero_add]
    have : Ideal.Quotient.mk J a = 1 := by
      rw [← map_one (Ideal.Quotient.mk J), ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hb,
        add_zero]
    rw [this, one_mul]
  refine ⟨h, fun n => Ideal.mem_inf.2 ⟨?_, ?_⟩⟩
  · revert n
    rw [mem_iff_mapHom, mapHom_levelExpr' p]
    simp_rw [keyI]
    rw [← mapHom_levelExpr' p, ← mem_iff_mapHom]; exact h1
  · revert n
    rw [mem_iff_mapHom, mapHom_levelExpr' p]
    simp_rw [keyJ]
    rw [← mapHom_levelExpr' p, ← mem_iff_mapHom]; exact h2

/-- **Finitely many pairwise coprime ideals.** -/
theorem hasLevelIdeal_biInf_iff {ι : Type*} [DecidableEq ι] (f : ArithmeticFunction R)
    (I : ι → Ideal R) (L : ℕ) (s : Finset ι)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → I i ⊔ I j = ⊤) :
    HasLevelIdeal p f (⨅ i ∈ s, I i) L ↔ ∀ i ∈ s, HasLevelIdeal p f (I i) L := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iInf_of_empty, iInf_top, IsEmpty.forall_iff, implies_true,
      iff_true]
    exact ⟨fun _ => 0, fun n => Submodule.mem_top⟩
  | insert a s ha ih =>
    rw [Finset.iInf_insert]
    have hc : I a ⊔ ⨅ i ∈ s, I i = ⊤ :=
      Ideal.sup_iInf_eq_top fun i hi => hcop a (Finset.mem_insert_self a s) i
        (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    rw [hasLevelIdeal_inf_iff p hc, ih (fun i hi j hj hij =>
      hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]
    simp only [Finset.mem_insert, forall_eq_or_imp]

/-- **Prop maxP, Chinese remainder form.** If `p^k R = ⨅_{i ∈ s} I_i` with the `I_i` pairwise
coprime, then for every `f` with `f(1)` a unit, `L_f(p, k)` is the largest of the counts modulo
the `I_i`. -/
theorem levelCount_eq_sup_ideal {ι : Type*} [DecidableEq ι] (f : ArithmeticFunction R)
    (hf : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) (I : ι → Ideal R) (s : Finset ι)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → I i ⊔ I j = ⊤)
    (hprod : (⨅ i ∈ s, I i) = Ideal.span {(p : R) ^ k}) :
    levelCount p (Ep p) f k = s.sup (fun i => levelCountIdeal p f (I i)) := by
  have hA := (hasLevel_iff_ideal p f k _).1
    (hasLevel_kempner_any p f (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 hf) hk)
  rw [← hprod] at hA
  have hne : ∀ i ∈ s, HasLevelIdeal p f (I i) (kempner p k - 1) :=
    (hasLevelIdeal_biInf_iff p f I _ s hcop).1 hA
  rw [levelCount_eq_ideal, ← hprod, levelCountIdeal]
  have hmem : ∀ i ∈ s, HasLevelIdeal p f (I i) (levelCountIdeal p f (I i)) :=
    fun i hi => Nat.sInf_mem (s := {L | HasLevelIdeal p f (I i) L}) ⟨_, hne i hi⟩
  apply le_antisymm
  · apply Nat.sInf_le
    rw [Set.mem_setOf_eq, hasLevelIdeal_biInf_iff p f I _ s hcop]
    intro i hi
    exact (hmem i hi).mono p (Finset.le_sup (f := fun i => levelCountIdeal p f (I i)) hi)
  · refine le_csInf ⟨_, hA⟩ fun L hL => Finset.sup_le fun i hi => ?_
    rw [Set.mem_setOf_eq, hasLevelIdeal_biInf_iff p f I _ s hcop] at hL
    exact Nat.sInf_le (hL i hi)

end Dir

end FrobLevel
