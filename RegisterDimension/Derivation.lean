import RegisterDimension.Conservation
import RegisterDimension.Vertex

/-!
# `d = 3` from the two postulates: Sec. IV of *The Dimension of Space from the Granularity of
Hilbert Space* (v16-34)

The register's least interaction (`Emission`): a string passes one notch to a new string, the
light, on an empty ring through the same cell.  Its three legs are the string before, the light,
and the string after.  Coordinates are chosen so that the string's ring and the light's ring are two
of the `d` rings through the cell; the orientation of the rings is a choice of coordinates.

* Postulate 1: a ring carries one string, so the light is on a ring other than the string's
  (`huv`) and the string after is not on the light's ring (`hafter`).
* An interaction exchanges momentum, so the light's mode number is not zero (`hκl`).
* Conservation (Postulate 1, no law depends on the global phase): along every ring the vertex
  intertwines the joint shifts (`hA`, `hmap`), and below the Planck momentum no sum wraps (`hwin`).
* Postulate 2: one cell per momentum, the equality of the two counts (`hpost`).

`Emission.finrank_legs` proves that the three momenta span a plane, and `three_from_postulates`
that `d = 3`.  `model` is an interaction of this form at `d = 3`, and `model_consistent` shows that
it meets Postulate 2, so the hypotheses can all be met together.
-/

open Module Submodule

namespace Register
namespace Derivation

/-- **The register's least interaction** (Sec. IV), along the `d` rings through its cell. -/
structure Emission (L d : ℕ) where
  /-- the ring of the string before -/
  u : Fin d
  /-- the ring of the light -/
  v : Fin d
  /-- a ring carries one string (Postulate 1): the light is not on the string's ring -/
  huv : u ≠ v
  /-- the mode number of the string before, along its ring -/
  κ : ℤ
  /-- the mode number of the light, along its ring -/
  κl : ℤ
  /-- an interaction exchanges momentum: the light's mode number is not zero -/
  hκl : κl ≠ 0
  /-- the components of the string after, one per ring -/
  after : Fin d → ℤ
  /-- a ring carries one string (Postulate 1): the string after is not on the light's ring -/
  hafter : ¬ ∃ t : ℝ, (fun w => (after w : ℝ)) = t • (Pi.single v 1 : Fin d → ℝ)
  /-- the vertex, along each ring -/
  A : Fin d → ((Fin 1 → ℤ) → ℂ) →ₗ[ℂ] ((Fin 2 → ℤ) → ℂ)
  /-- no law depends on the global phase: the vertex intertwines the joint shifts -/
  hA : ∀ w, A w ∘ₗ Conservation.jointShift 1 = Conservation.jointShift 2 ∘ₗ A w
  /-- the amplitude of the vertex, along each ring -/
  c : Fin d → ℂ
  hc : ∀ w, c w ≠ 0
  /-- the legs have definite momenta: the vertex takes the incoming mode to the outgoing one -/
  hmap : ∀ w, A w (Conservation.jointMode L (fun _ => (Pi.single u κ : Fin d → ℤ) w))
    = c w • Conservation.jointMode L ![(Pi.single v κl : Fin d → ℤ) w, after w]
  /-- the momenta lie below the Planck momentum, as every observable momentum does -/
  hwin : ∀ w, -(L : ℤ) < 2 * (Pi.single u κ : Fin d → ℤ) w ∧
    2 * (Pi.single u κ : Fin d → ℤ) w ≤ L ∧
    -(L : ℤ) < 2 * ((Pi.single v κl : Fin d → ℤ) w + after w) ∧
    2 * ((Pi.single v κl : Fin d → ℤ) w + after w) ≤ L

/-- the three momenta as vectors, counted so that they sum to zero: the string before, minus the
light, minus the string after -/
noncomputable def Emission.legs {L d : ℕ} (X : Emission L d) : Fin 3 → (Fin d → ℝ) :=
  ![fun w => ((Pi.single X.u X.κ : Fin d → ℤ) w : ℝ),
    -(fun w => ((Pi.single X.v X.κl : Fin d → ℤ) w : ℝ)),
    -(fun w => (X.after w : ℝ))]

/-- **Conservation along every ring**: the string before carries what the light and the string
after carry. -/
theorem Emission.conserve {L d : ℕ} (X : Emission L d) (hL : 0 < L) (w : Fin d) :
    (Pi.single X.u X.κ : Fin d → ℤ) w = (Pi.single X.v X.κl : Fin d → ℤ) w + X.after w := by
  have h := Conservation.total_mode_conserved L hL (X.A w) (X.hA w)
    (fun _ => (Pi.single X.u X.κ : Fin d → ℤ) w) ![(Pi.single X.v X.κl : Fin d → ℤ) w, X.after w]
    (X.c w) (X.hc w) (X.hmap w)
  simp only [Fin.sum_univ_one, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  obtain ⟨h1, h2, h3, h4⟩ := X.hwin w
  exact Conservation.eq_of_window L h1 h2 h3 h4 h

/-- **The three momenta span a plane**, so they are not collinear (Sec. IV). -/
theorem Emission.finrank_legs {L d : ℕ} (X : Emission L d) (hL : 0 < L) :
    finrank ℝ (span ℝ (Set.range X.legs)) = 2 := by
  have hvu : X.v ≠ X.u := X.huv.symm
  -- conservation as vectors: the string after is the string before minus the light
  have hafter : (fun w => (X.after w : ℝ)) =
      (fun w => ((Pi.single X.u X.κ : Fin d → ℤ) w : ℝ)) -
        (fun w => ((Pi.single X.v X.κl : Fin d → ℤ) w : ℝ)) := by
    funext w
    simp only [Pi.sub_apply]
    have h' : ((Pi.single X.u X.κ : Fin d → ℤ) w : ℝ)
        = ((Pi.single X.v X.κl : Fin d → ℤ) w : ℝ) + (X.after w : ℝ) := by
      exact_mod_cast X.conserve hL w
    linarith
  -- the string before moves: at rest, the string after would be on the light's ring
  have hκ : X.κ ≠ 0 := by
    intro h0
    apply X.hafter
    refine ⟨-(X.κl : ℝ), ?_⟩
    rw [hafter]
    funext w
    by_cases hw : w = X.v
    · subst hw
      simp [h0]
    · simp [h0, Pi.single_eq_of_ne hw]
  -- the string before and the light are independent
  have hind : LinearIndependent ℝ (X.legs ∘ Fin.castSucc) := by
    have e1 : X.legs ∘ Fin.castSucc = ![fun w => ((Pi.single X.u X.κ : Fin d → ℤ) w : ℝ),
        -(fun w => ((Pi.single X.v X.κl : Fin d → ℤ) w : ℝ))] := by
      funext i
      fin_cases i <;> rfl
    rw [e1]
    apply LinearIndependent.pair_iff.2
    intro s t hst
    have hu : s * (X.κ : ℝ) = 0 := by
      have h := congrFun hst X.u
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne X.huv, Int.cast_zero, neg_zero, mul_zero,
        add_zero] at h
      exact h
    have hv : t * (X.κl : ℝ) = 0 := by
      have h := congrFun hst X.v
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne hvu, Int.cast_zero, mul_zero, zero_add,
        mul_neg, neg_eq_zero] at h
      exact h
    constructor
    · rcases mul_eq_zero.1 hu with h | h
      · exact h
      · exact absurd (by exact_mod_cast h) hκ
    · rcases mul_eq_zero.1 hv with h | h
      · exact h
      · exact absurd (by exact_mod_cast h) X.hκl
  -- the three momenta sum to zero
  have hsum : ∑ i, X.legs i = 0 := by
    rw [Fin.sum_univ_three]
    show (fun w => ((Pi.single X.u X.κ : Fin d → ℤ) w : ℝ)) +
        -(fun w => ((Pi.single X.v X.κl : Fin d → ℤ) w : ℝ)) + -(fun w => (X.after w : ℝ)) = 0
    rw [hafter]
    abel
  exact Vertex.finrank_span_eq_of_sum_zero 2 X.legs hsum hind

/-- **Space has three dimensions, from the two postulates** (Sec. IV): the register's least
interaction, with Postulate 2 as the equality of the two counts, gives `d = 3`. -/
theorem three_from_postulates {L d : ℕ} (hL : 2 ≤ L) (X : Emission L d)
    (hpost : Fintype.card (Vertex.alphabet L (finrank ℝ (span ℝ (Set.range X.legs))))
      = Fintype.card (Vertex.cells L d)) : d = 3 := by
  rw [X.finrank_legs (by omega), Vertex.alphabet_card L 2 (by norm_num), Vertex.cells_card]
    at hpost
  have := Vertex.span_of_postulate L 2 d hL hpost
  omega

/-! ### A model: the hypotheses can all be met together -/

/-- the vertex of the model along ring `w`, from `Conservation.vertex_exists` -/
theorem model_vertex (w : Fin 3) :
    ∃ A : ((Fin 1 → ℤ) → ℂ) →ₗ[ℂ] ((Fin 2 → ℤ) → ℂ),
      A ∘ₗ Conservation.jointShift 1 = Conservation.jointShift 2 ∘ₗ A ∧
      A (Conservation.jointMode 5 (fun _ => (Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) w))
        = (1 : ℂ) • Conservation.jointMode 5
          ![(Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) w - (![1, -1, 0] : Fin 3 → ℤ) w,
            (![1, -1, 0] : Fin 3 → ℤ) w] :=
  Conservation.vertex_exists 5 ((Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) w)
    ((![1, -1, 0] : Fin 3 → ℤ) w)

/-- **A least interaction at `d = 3`**: at `L = 5` the string on ring 0 with mode 1 passes one
notch to the light on ring 1 and continues with components `(1, −1, 0)`. -/
noncomputable def model : Emission 5 3 where
  u := 0
  v := 1
  huv := by decide
  κ := 1
  κl := 1
  hκl := by decide
  after := ![1, -1, 0]
  hafter := by
    rintro ⟨t, ht⟩
    have h0 := congrFun ht 0
    simp at h0
  A := fun w => Classical.choose (model_vertex w)
  hA := fun w => (Classical.choose_spec (model_vertex w)).1
  c := fun _ => 1
  hc := fun _ => one_ne_zero
  hmap := by
    intro w
    have h := (Classical.choose_spec (model_vertex w)).2
    have e : (Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) w - (![1, -1, 0] : Fin 3 → ℤ) w
        = (Pi.single (1 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) w := by
      fin_cases w <;> decide
    rw [← e]
    exact h
  hwin := by
    intro w
    fin_cases w <;> decide

/-- **The model meets Postulate 2**, so the hypotheses of `three_from_postulates` are consistent. -/
theorem model_consistent :
    Fintype.card (Vertex.alphabet 5 (finrank ℝ (span ℝ (Set.range model.legs))))
      = Fintype.card (Vertex.cells 5 3) := by
  rw [model.finrank_legs (by norm_num), Vertex.alphabet_card 5 2 (by norm_num), Vertex.cells_card]

end Derivation
end Register
