import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# The dimension of an interaction: Sec. IV of *The Dimension of Space from the Granularity of
Hilbert Space* (v16-34)

The count of Sec. IV, with every step a theorem and the junctions between the steps checked too.
Two definitions carry the paper's reading of the register into Lean: the readings of one leg's
momentum in a span of dimension `s` are a magnitude with `L` values and `s − 1` angles with `L`
values each (`alphabet`), and the cells of the sphere are `L` values in each of `d − 1` coordinates
(`cells`).  So a leg has `L^s` momenta (`alphabet_card`) and the sphere has `L^(d−1)` cells
(`cells_card`, Eq. (cells)).  Postulate 2 puts one cell on each momentum, so the two counts are
equal, and `L^s = L^(d−1)` gives `s = d − 1` (`span_of_postulate`).  Conserved momenta, `n + 1`
of them summing to zero, span at most `n` dimensions (`finrank_span_le_of_sum_zero`), exactly `n`
when the first `n` are independent (`finrank_span_eq_of_sum_zero`).  Given the momenta of a
vertex and Postulate 2 as the equality of the two counts, with `s` the dimension of their span,
`d = n + 1` (`dimension_eq_legs`, Eq. (nk)), and the three-leg vertex of the register, whose
momenta are not collinear, gives `d = 3` (`three`, Eq. (three)).  Also: counting the orientation
of the plane as well, `2(d − 2)` more angles, would break the count (`orientation_not_counted`);
the coincidence of two uncorrelated strings at one cell is one pair in `L` (`coincidence`,
Eq. (coincidence)) and, if two rings share two cells, `2/L²` (`coincidence_two_cells`); and a law
that commutes with the shift preserves the shift's eigenspaces, so the mode number is conserved
(`eigenspace_preserved`; `Ring.joint_mode` shows the mode numbers of two strings add).

The space is any finite-dimensional real vector space: the linear structure at the point of the
vertex that the setting assumes, and nothing more.  What Lean cannot check is that the two
definitions are the right model of the register; it checks everything that follows from them.
-/

open Module Submodule Finset

namespace Register
namespace Vertex

/-- the readings of one leg's momentum in a span of dimension `s` (Sec. IV): a magnitude with `L`
values and `s − 1` angles with `L` values each -/
abbrev alphabet (L s : ℕ) := Fin L × (Fin (s - 1) → Fin L)

/-- the cells of the sphere in `d` dimensions, Eq. (cells): `L` values in each of `d − 1`
coordinates -/
abbrev cells (L d : ℕ) := Fin (d - 1) → Fin L

/-- **A leg has `L^s` momenta** (Sec. IV). -/
theorem alphabet_card (L s : ℕ) (hs : 1 ≤ s) : Fintype.card (alphabet L s) = L ^ s := by
  show Fintype.card (Fin L × (Fin (s - 1) → Fin L)) = L ^ s
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_succ']
  congr 1
  omega

/-- the alphabet of a leg whose momentum is confined to a point: a magnitude only, `L` readings -/
theorem alphabet_card_zero (L : ℕ) : Fintype.card (alphabet L 0) = L := by
  show Fintype.card (Fin L × (Fin 0 → Fin L)) = L
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_zero, mul_one]

/-- **The sphere has `L^(d−1)` cells**, Eq. (cells). -/
theorem cells_card (L d : ℕ) : Fintype.card (cells L d) = L ^ (d - 1) := by
  show Fintype.card (Fin (d - 1) → Fin L) = L ^ (d - 1)
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **Postulate 2 fixes the span** (Sec. IV): one cell per momentum, `L^s = L^(d−1)`, gives
`s = d − 1`. -/
theorem span_of_postulate (L s d : ℕ) (hL : 2 ≤ L) (h : L ^ s = L ^ (d - 1)) : s = d - 1 :=
  Nat.pow_right_injective hL h

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **Conserved momenta span one dimension less than their number** (Sec. IV): `n + 1` momenta
that sum to zero span a subspace of dimension at most `n`. -/
theorem finrank_span_le_of_sum_zero (n : ℕ) (v : Fin (n + 1) → V) (hsum : ∑ i, v i = 0) :
    finrank ℝ (span ℝ (Set.range v)) ≤ n := by
  have hlast : v (Fin.last n) ∈ span ℝ (Set.range (v ∘ Fin.castSucc)) := by
    rw [Fin.sum_univ_castSucc] at hsum
    have e : v (Fin.last n) = -∑ i : Fin n, v (Fin.castSucc i) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hsum
    rw [e]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun i _ => subset_span ⟨i, rfl⟩))
  have hle : span ℝ (Set.range v) ≤ span ℝ (Set.range (v ∘ Fin.castSucc)) := by
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact subset_span ⟨j, rfl⟩
    · exact hlast
  calc finrank ℝ (span ℝ (Set.range v))
      ≤ finrank ℝ (span ℝ (Set.range (v ∘ Fin.castSucc))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin n) := finrank_range_le_card _
    _ = n := Fintype.card_fin n

/-- **With no further relation the span is exactly `n`** (Sec. IV): if the first `n` momenta are
linearly independent, `n + 1` momenta that sum to zero span a subspace of dimension `n`. -/
theorem finrank_span_eq_of_sum_zero (n : ℕ) (v : Fin (n + 1) → V) (hsum : ∑ i, v i = 0)
    (hind : LinearIndependent ℝ (v ∘ Fin.castSucc)) :
    finrank ℝ (span ℝ (Set.range v)) = n := by
  apply le_antisymm (finrank_span_le_of_sum_zero n v hsum)
  calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
    _ = finrank ℝ (span ℝ (Set.range (v ∘ Fin.castSucc))) := (finrank_span_eq_card hind).symm
    _ ≤ finrank ℝ (span ℝ (Set.range v)) := by
        apply Submodule.finrank_mono
        rw [span_le]
        rintro _ ⟨j, rfl⟩
        exact subset_span ⟨Fin.castSucc j, rfl⟩

/-- **A vertex with `n + 1` legs needs `n + 1` dimensions**, Eq. (nk) (Sec. IV).  Given the momenta
`v` of the legs, which sum to zero, with the first `n` independent, and Postulate 2 as the equality
of the two counts, one cell per momentum, with the span's dimension in the alphabet: `d = n + 1`.
The proof computes the span's dimension, `n`, turns both counts into powers of `L`, and reads off
`n = d − 1`. -/
theorem dimension_eq_legs (L n d : ℕ) (hL : 2 ≤ L) (hn : 1 ≤ n) (v : Fin (n + 1) → V)
    (hsum : ∑ i, v i = 0) (hind : LinearIndependent ℝ (v ∘ Fin.castSucc))
    (hpost : Fintype.card (alphabet L (finrank ℝ (span ℝ (Set.range v)))) =
      Fintype.card (cells L d)) : d = n + 1 := by
  have hs : finrank ℝ (span ℝ (Set.range v)) = n := finrank_span_eq_of_sum_zero n v hsum hind
  have h1 := alphabet_card L (finrank ℝ (span ℝ (Set.range v))) (by rw [hs]; exact hn)
  rw [h1, cells_card, hs] at hpost
  have := span_of_postulate L n d hL hpost
  omega

/-- **Space has three dimensions**, Eq. (three) (Sec. IV): the register's vertex has three legs;
their momenta sum to zero and two of them are independent, so the momenta span a plane; with
Postulate 2, `d = 3`. -/
theorem three (L d : ℕ) (hL : 2 ≤ L) (v : Fin 3 → V) (hsum : ∑ i, v i = 0)
    (hind : LinearIndependent ℝ (v ∘ Fin.castSucc))
    (hpost : Fintype.card (alphabet L (finrank ℝ (span ℝ (Set.range v)))) =
      Fintype.card (cells L d)) : d = 3 :=
  dimension_eq_legs L 2 d hL (by norm_num) v hsum hind hpost

/-- **Counting the orientation of the plane would break the count** (Sec. IV): a plane's
orientation adds `2(d − 2)` angles, and `L^(2d−2)` readings equal `L^(d−1)` cells only at `d = 1`,
where there is no plane.  The count `2(d − 2)` is the paper's; the file checks the arithmetic. -/
theorem orientation_not_counted (L d : ℕ) (hL : 2 ≤ L) (hd : 1 ≤ d)
    (h : L ^ (2 * d - 2) = L ^ (d - 1)) : d = 1 := by
  have := Nat.pow_right_injective hL h
  omega

/-- **The coincidence of two strings at one cell**, Eq. (coincidence) (Sec. IV): a mode is at each
cell with probability `1/L`, so two uncorrelated strings on one ring are at the same cell with
probability `∑_{j=1}^{L} (1/L)(1/L) = 1/L`. -/
theorem coincidence (L : ℕ) (hL : 0 < L) :
    ∑ _j : Fin L, ((1 : ℝ) / L) * (1 / L) = 1 / L := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    mul_one_div_cancel hL', one_mul]

/-- **Two rings in different planes share at most two cells** (`Planes.two_planes_meet`), so the
coincidence of uncorrelated strings on them is at most `2/L²` (Sec. IV). -/
theorem coincidence_two_cells (L : ℕ) :
    ∑ _j : Fin 2, ((1 : ℝ) / L) * (1 / L) = 2 / L ^ 2 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Noether on `ℤ_L`** (Sec. IV): a law `A` that commutes with the shift `X` maps each eigenspace
of `X` into itself, so the mode number, the eigenvalue of `X`, is conserved. -/
theorem eigenspace_preserved {W : Type*} [AddCommGroup W] [Module ℂ W] (X A : W →ₗ[ℂ] W)
    (hcomm : ∀ w, A (X w) = X (A w)) (μ : ℂ) (w : W) (hw : w ∈ Module.End.eigenspace X μ) :
    A w ∈ Module.End.eigenspace X μ := by
  rw [Module.End.mem_eigenspace_iff] at hw ⊢
  rw [← hcomm, hw, map_smul]

end Vertex
end Register
