import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Two rings share at most two cells: Sec. IV of *The Dimension of Space from the Granularity of
Hilbert Space* (v16-34)

A ring of the sphere of Postulate 2 lies in a plane through the center.  Two rings in different
planes meet only where the planes meet, which is at most a line, and a line meets the sphere in at
most two opposite points (`two_planes_meet`).  So two strings on rings in different planes can
coincide at no more than two cells, and the rate `2/L²` of `Vertex.coincidence_two_cells` is an upper
bound.
-/

open Module Submodule

namespace Register
namespace Planes

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Two different planes meet in at most two opposite points of the unit sphere.** -/
theorem two_planes_meet (P Q : Submodule ℝ W) (hP : finrank ℝ P = 2) (hQ : finrank ℝ Q = 2)
    (hPQ : P ≠ Q) {x y : W} (hx : x ∈ P ⊓ Q) (hy : y ∈ P ⊓ Q) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) :
    y = x ∨ y = -x := by
  -- the planes meet in at most a line
  have hdim : finrank ℝ (P ⊓ Q : Submodule ℝ W) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h1 : finrank ℝ P ≤ finrank ℝ (P ⊓ Q : Submodule ℝ W) := by omega
    have h2 : finrank ℝ Q ≤ finrank ℝ (P ⊓ Q : Submodule ℝ W) := by omega
    have eP : P ⊓ Q = P := Submodule.eq_of_le_of_finrank_le inf_le_left h1
    have eQ : P ⊓ Q = Q := Submodule.eq_of_le_of_finrank_le inf_le_right h2
    exact hPQ (eP.symm.trans eQ)
  -- the line is spanned by `x`
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx1
    exact zero_ne_one hx1
  have hspan : (ℝ ∙ x) = P ⊓ Q := by
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hx
    · rw [finrank_span_singleton hx0]
      exact hdim
  have hy' : y ∈ ℝ ∙ x := by
    rw [hspan]
    exact hy
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hy'
  have hnorm : |t| = 1 := by
    have h := congrArg norm ht
    rw [norm_smul, Real.norm_eq_abs, hx1, hy1, mul_one] at h
    exact h
  rcases (abs_eq (zero_le_one' ℝ)).1 hnorm with h | h
  · left
    rw [← ht, h, one_smul]
  · right
    rw [← ht, h, neg_one_smul]

end Planes
end Register
