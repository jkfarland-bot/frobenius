module

/-
Run r25, seat L4: ledger R-086, Proposition T (note Proposition 6.x, `prop:lifts` (a)).

`L_f(p, k)` depends on the Frobenius lift `σ` only through its image `B = σ(A)`, and a ring
isomorphism `θ : A ≃+* A'` carries `L^B_f` to `L^{θ(B)}_{θ f}`. Also: `L_f(p, k)` depends on `f`
only modulo `p ^ k`.

Everything is abstract (a commutative ring `A`, any ring endomorphism `σ`); no hypothesis on `σ`
is needed. Builds on seat L1's `Found.lean` (definitions `HasLevel`, `MonicAnn`, `levelCount`).
-/
public import Mathlib
public import Frobenius.Levels.Found

@[expose] public section

namespace FrobLevel

open Polynomial

section RangeOnly

variable {A : Type*} [CommRing A]

/-- A level identity for `σ` is one for every `σ'` whose image contains that of `σ`. -/
theorem HasLevel.of_range_le {p : ℕ} {σ σ' : A →+* A} (hle : σ.range ≤ σ'.range) {f : A}
    {k L : ℕ} (h : HasLevel p σ f k L) : HasLevel p σ' f k L := by
  obtain ⟨g, hg⟩ := h
  have : ∀ z, ∃ g', σ' g' = σ (g z) := fun z =>
    RingHom.mem_range.1 (hle (RingHom.mem_range_self σ (g z)))
  choose g' hg' using this
  exact ⟨g', by simpa only [hg'] using hg⟩

/-- **Prop T (a), first half.** `HasLevel` depends on `σ` only through `B = σ(A)`. -/
theorem hasLevel_iff_of_range_eq {p : ℕ} {σ σ' : A →+* A} (h : σ.range = σ'.range) {f : A}
    {k L : ℕ} : HasLevel p σ f k L ↔ HasLevel p σ' f k L :=
  ⟨HasLevel.of_range_le h.le, HasLevel.of_range_le h.ge⟩

/-- **Prop T (a), first half, for the count.** `L_f(p, k)` depends on `σ` only through `B`. -/
theorem levelCount_eq_of_range_eq {p : ℕ} {σ σ' : A →+* A} (h : σ.range = σ'.range) (f : A)
    (k : ℕ) : levelCount p σ f k = levelCount p σ' f k := by
  unfold levelCount
  rw [show {L | HasLevel p σ f k L} = {L | HasLevel p σ' f k L} from
    Set.ext fun _ => hasLevel_iff_of_range_eq h]

/-- The monic form also depends only on `B`. -/
theorem monicAnn_iff_of_range_eq {p : ℕ} {σ σ' : A →+* A} (h : σ.range = σ'.range) {u : A}
    {k m : ℕ} : MonicAnn p σ u k m ↔ MonicAnn p σ' u k m := by
  have hB : ∀ P : A[X], P ∈ BPoly σ ↔ P ∈ BPoly σ' := fun P => by
    rw [mem_BPoly_iff, mem_BPoly_iff]
    exact forall_congr' fun i => by rw [frobImage, frobImage, h]
  exact exists_congr fun P => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_left fun _ => hB P

/-- `L_f(p, k)` depends on `f` only modulo `p ^ k`. -/
theorem hasLevel_congr {p : ℕ} {σ : A →+* A} {f f' : A} {k : ℕ} (hff : (p : A) ^ k ∣ f - f')
    (L : ℕ) : HasLevel p σ f k L ↔ HasLevel p σ f' k L := by
  set π := Ideal.Quotient.mk (Ideal.span {(p : A) ^ k})
  have hdvd : ∀ a : A, (p : A) ^ k ∣ a ↔ π a = 0 := fun a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hπ : π f = π f' := by rw [← sub_eq_zero, ← map_sub]; exact (hdvd _).1 hff
  have key : ∀ g : ℕ → A, π (1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * σ (g z))
      = π (1 - f' * ∑ z ∈ Finset.range (L + 1), f' ^ z * σ (g z)) := by
    intro g
    simp only [map_sub, map_one, map_mul, map_sum, map_pow, hπ]
  exact exists_congr fun g => by rw [hdvd, hdvd, key]

theorem levelCount_congr {p : ℕ} {σ : A →+* A} {f f' : A} {k : ℕ} (hff : (p : A) ^ k ∣ f - f') :
    levelCount p σ f k = levelCount p σ f' k := by
  unfold levelCount
  rw [show {L | HasLevel p σ f k L} = {L | HasLevel p σ f' k L} from
    Set.ext fun L => hasLevel_congr hff L]

end RangeOnly

section Transport

variable {A A' : Type*} [CommRing A] [CommRing A']

/-- The conjugate `θ σ θ⁻¹` of an endomorphism by a ring isomorphism. -/
def conjLift (θ : A ≃+* A') (σ : A →+* A) : A' →+* A' :=
  (θ : A →+* A').comp (σ.comp (θ.symm : A' →+* A))

@[simp] theorem conjLift_apply (θ : A ≃+* A') (σ : A →+* A) (a : A') :
    conjLift θ σ a = θ (σ (θ.symm a)) := rfl

/-- The image of the conjugate lift is `θ(B)`. -/
theorem range_conjLift (θ : A ≃+* A') (σ : A →+* A) :
    (conjLift θ σ).range = σ.range.map (θ : A →+* A') := by
  ext y
  simp only [RingHom.mem_range, Subring.mem_map, conjLift_apply]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨σ (θ.symm a), ⟨θ.symm a, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, rfl⟩, rfl⟩; exact ⟨θ a, by simp⟩

/-- A conjugate of a Frobenius lift is a Frobenius lift. -/
theorem IsFrobLift.conj {p : ℕ} {σ : A →+* A} (h : IsFrobLift p σ) (θ : A ≃+* A') :
    IsFrobLift p (conjLift θ σ) := by
  intro a
  have := map_dvd (θ : A →+* A') (h (θ.symm a))
  simpa using this

theorem conjLift_symm_conjLift (θ : A ≃+* A') (σ : A →+* A) :
    conjLift θ.symm (conjLift θ σ) = σ := by
  ext a; simp

theorem HasLevel.conj {p : ℕ} {σ : A →+* A} {f : A} {k L : ℕ} (h : HasLevel p σ f k L)
    (θ : A ≃+* A') : HasLevel p (conjLift θ σ) (θ f) k L := by
  obtain ⟨g, hg⟩ := h
  refine ⟨fun z => θ (g z), ?_⟩
  have := map_dvd (θ : A →+* A') hg
  simpa using this

/-- **Prop T (a), second half.** `L^{θ(B)}_{θ f} = L^B_f` for the conjugate lift. -/
theorem hasLevel_conj_iff {p : ℕ} {σ : A →+* A} {f : A} {k L : ℕ} (θ : A ≃+* A') :
    HasLevel p (conjLift θ σ) (θ f) k L ↔ HasLevel p σ f k L := by
  refine ⟨fun h => ?_, fun h => h.conj θ⟩
  have := h.conj θ.symm
  rwa [conjLift_symm_conjLift, RingEquiv.symm_apply_apply] at this

theorem levelCount_conj {p : ℕ} (θ : A ≃+* A') (σ : A →+* A) (f : A) (k : ℕ) :
    levelCount p (conjLift θ σ) (θ f) k = levelCount p σ f k := by
  unfold levelCount
  rw [show {L | HasLevel p (conjLift θ σ) (θ f) k L} = {L | HasLevel p σ f k L} from
    Set.ext fun _ => hasLevel_conj_iff θ]

/-- **Prop T (a), as stated in the note.** If `σ'` is any endomorphism of `A'` with image
`θ(B)`, `B = σ(A)`, then `L^{σ'}_{θ f}(p, k) = L^{σ}_f(p, k)`. -/
theorem levelCount_eq_of_range_eq_map {p : ℕ} (θ : A ≃+* A') (σ : A →+* A) (σ' : A' →+* A')
    (h : σ'.range = σ.range.map (θ : A →+* A')) (f : A) (k : ℕ) :
    levelCount p σ' (θ f) k = levelCount p σ f k := by
  rw [levelCount_eq_of_range_eq (h.trans (range_conjLift θ σ).symm), levelCount_conj]

end Transport

end FrobLevel
