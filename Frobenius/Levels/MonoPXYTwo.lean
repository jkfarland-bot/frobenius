module

/- Seat L10v: the hypothesis p ≥ 3 in L10.liftPXY_not_monomial is necessary: at p = 2,
x ↦ x^2 + 2xy, y ↦ y^2 satisfies σ(x + y) = (x + y)^2, so m = (x + y, y) is monomial data. -/
public import Mathlib
public import Frobenius.Levels.MonoPXY

@[expose] public section

namespace FrobLevel
open MvPowerSeries FrobLevel L10

theorem liftPXY_two_monomial :
    ∃ m : Fin 2 → MvPowerSeries (Fin 2) ℤ_[2],
      (∀ i, m i ^ 2 ∈ frobImage (liftPXY (p := 2))) ∧ IsUnit (linMat m) := by
  refine ⟨![X 0 + X 1, X 1], fun i => ?_, ?_⟩
  · fin_cases i
    · refine ⟨X 0 + X 1, ?_⟩
      simp only [map_add, liftPXY_X0, liftPXY_X1]
      simp; ring
    · exact ⟨X 1, by simp [liftPXY_X1]⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two]
    have hc : ∀ (i j : Fin 2), coeff (Finsupp.single j 1) (X i : MvPowerSeries (Fin 2) ℤ_[2])
        = if i = j then 1 else 0 := by
      intro i j
      rw [coeff_X]
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg, if_neg h]
        intro hh; exact h (Finsupp.single_left_injective one_ne_zero hh).symm
    simp [linMat, hc]

end FrobLevel
