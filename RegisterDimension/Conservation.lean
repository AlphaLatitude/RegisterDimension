import RegisterDimension.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The setting and conservation, from Postulate 1: Secs. II and IV of *The Dimension of Space
from the Granularity of Hilbert Space* (v16-34)

* **The shifts through a cell commute** (`shifts_commute`, Sec. II): the register records a
  string's place only by its phase on each ring through its cell, and no information is lost, so
  the record is one-to-one; a shift along ring `u` advances the phase on `u` by one notch and leaves
  the others.  Two orders of two shifts leave the same record, so they reach the same place.
  `turn_comm` is the model in which a place is its record, and shows the hypotheses are consistent.
* **A momentum has one whole-number component per ring** (`eigenvalue_root`, `productMode_shift`,
  Sec. IV): momentum generates translation, so a state of definite momentum is an eigenvector of the
  shift along every ring through the cell; the ring closes after `L` cells, so each eigenvalue is an
  `L`th root of unity `e^{2πiκ_u/L}` with `κ_u` whole, and every tuple of whole numbers occurs.
* **Noether on `ℤ_L`** (`total_mode_conserved`): no law depends on the global phase, and moving its
  origin one cell on is the joint shift, so the vertex intertwines the joint shifts along every ring;
  a joint mode is an eigenvector of the joint shift with eigenvalue `e^{−2πiΣκ/L}`
  (`jointMode_shift`), and equal roots of unity are equal numbers modulo `L` (`root_eq_iff`), so the
  total mode number is conserved modulo `L`.  `vertex_exists` gives such a vertex.
* Below the Planck momentum no sum wraps (`eq_of_window`), so for the three-leg vertex
  `κ_in = κ_out,1 + κ_out,2` along every ring (`three_leg_conservation`), and the momenta sum to
  zero as vectors (`sum_zero_of_components`).
-/

open Complex Real

namespace Register
namespace Conservation

/-! ### The setting: a string's place, and the commuting shifts -/

/-- a string's place at a cell: its phase on each of the `d` rings through the cell -/
abbrev Place (L d : ℕ) := Fin d → ZMod L

/-- turning the ring of direction `u` one notch: the phase on `u` advances by one notch and the
other phases do not change -/
def turn {L d : ℕ} (u : Fin d) (x : Place L d) : Place L d := x + Pi.single u 1

/-- **The shifts of the rings through a common cell commute** (Sec. II).  `rec x` is the record of
the place `x`, its phase on each ring through the cell; `rec` is one-to-one, since no information
is lost (the tick is unitary); a shift along ring `u` advances the phase on `u` by one notch and
leaves the phases on the other rings. -/
theorem shifts_commute {P : Type*} {L d : ℕ} (rec : P → Fin d → ZMod L)
    (hrec : Function.Injective rec) (T : Fin d → P → P)
    (hT : ∀ u x, rec (T u x) = rec x + Pi.single u 1) (u v : Fin d) (x : P) :
    T u (T v x) = T v (T u x) := by
  apply hrec
  rw [hT, hT, hT, hT]
  abel

/-- the model in which a place is its record: the hypotheses of `shifts_commute` hold -/
theorem turn_comm {L d : ℕ} (u v : Fin d) (x : Place L d) :
    turn u (turn v x) = turn v (turn u x) :=
  shifts_commute id Function.injective_id turn (fun _ _ => rfl) u v x

/-! ### A momentum has one whole-number component per ring -/

/-- iterating an eigenvalue relation along one ring -/
theorem pow_iterate {d : ℕ} (f : (Fin d → ℤ) → ℂ) (e : Fin d → ℤ) (lam : ℂ)
    (h : ∀ j, f (j - e) = lam * f j) :
    ∀ (n : ℕ) (j : Fin d → ℤ), f (j - (n : ℤ) • e) = lam ^ n * f j := by
  intro n
  induction n with
  | zero =>
    intro j
    simp
  | succ n ih =>
    intro j
    have e1 : j - ((n + 1 : ℕ) : ℤ) • e = (j - (n : ℤ) • e) - e := by
      push_cast
      rw [add_smul, one_smul]
      abel
    rw [e1, h, ih, pow_succ]
    ring

/-- **The eigenvalue of a shift is a root of unity with a whole number** (Sec. IV): a state on the
cells, periodic along ring `u` with period `L` (the ring closes), that is an eigenvector of the
shift along `u` has eigenvalue `e^{2πiκ/L}` for a whole number `κ`. -/
theorem eigenvalue_root (L : ℕ) (hL : 0 < L) {d : ℕ} (f : (Fin d → ℤ) → ℂ) (u : Fin d) (lam : ℂ)
    (hper : ∀ j, f (j + (L : ℤ) • Pi.single u 1) = f j)
    (heig : ∀ j, f (j - Pi.single u 1) = lam * f j) (hf : f ≠ 0) :
    ∃ κ : ℤ, lam = Ring.root L κ := by
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (funext hcon)
  have h1 := pow_iterate f (Pi.single u 1) lam heig L j
  have h2 := hper (j - (L : ℤ) • Pi.single u 1)
  rw [sub_add_cancel] at h2
  rw [← h2] at h1
  have hpow : lam ^ L = 1 := by
    have h3 : (lam ^ L - 1) * f j = 0 := by
      rw [sub_mul, ← h1, one_mul, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd h4 hj
  have hprim := Complex.isPrimitiveRoot_exp L hL.ne'
  have : NeZero L := ⟨hL.ne'⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hpow
  refine ⟨i, ?_⟩
  rw [← hi]
  unfold Ring.root
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- the state of definite momentum with whole numbers `κ`, one per ring through the cell -/
noncomputable def productMode (L : ℕ) {d : ℕ} (κ : Fin d → ℤ) : (Fin d → ℤ) → ℂ :=
  fun j => ∏ w, Ring.mode L (κ w) (j w)

/-- **Every tuple of whole numbers is a momentum**: the product of modes is an eigenvector of the
shift along every ring, with eigenvalue `e^{−2πiκ_u/L}` along `u`. -/
theorem productMode_shift (L : ℕ) {d : ℕ} (κ : Fin d → ℤ) (u : Fin d) (j : Fin d → ℤ) :
    productMode L κ (j - Pi.single u 1) = Ring.root L (-κ u) * productMode L κ j := by
  unfold productMode
  have h : ∀ w : Fin d, Ring.mode L (κ w) ((j - Pi.single u 1 : Fin d → ℤ) w)
      = (if w = u then Ring.root L (-κ w) else 1) * Ring.mode L (κ w) (j w) := by
    intro w
    by_cases hw : w = u
    · subst hw
      rw [ite_eq_left rfl, Pi.sub_apply, Pi.single_eq_same]
      have := Ring.shift_eigen L (κ w) (j w)
      unfold Ring.shift at this
      exact this
    · rw [ite_eq_right hw, one_mul, Pi.sub_apply, Pi.single_eq_of_ne hw, sub_zero]
  rw [Finset.prod_congr rfl (fun w _ => h w), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

/-! ### The joint shift and the joint modes of several carriers along one direction -/

/-- the joint shift of `k` carriers along one direction: every carrier moves one cell on -/
def jointShift (k : ℕ) : ((Fin k → ℤ) → ℂ) →ₗ[ℂ] ((Fin k → ℤ) → ℂ) where
  toFun f := fun j => f (fun i => j i - 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- the joint mode of `k` carriers with mode numbers `κ`: the product of their modes -/
noncomputable def jointMode (L : ℕ) {k : ℕ} (κ : Fin k → ℤ) : (Fin k → ℤ) → ℂ :=
  fun j => ∏ i, Ring.mode L (κ i) (j i)

/-- roots multiply as their numbers add, for any number of terms -/
theorem root_sum (L : ℕ) : ∀ {k : ℕ} (κ : Fin k → ℤ),
    Ring.root L (∑ i, κ i) = ∏ i, Ring.root L (κ i) := by
  intro k
  induction k with
  | zero =>
    intro κ
    simp [Ring.root_zero]
  | succ n ih =>
    intro κ
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ, Ring.root_add, ih]

theorem mode_at_zero (L : ℕ) (κ : ℤ) : Ring.mode L κ 0 = 1 := by
  unfold Ring.mode
  simp

theorem jointMode_ne_zero (L : ℕ) {k : ℕ} (κ : Fin k → ℤ) : jointMode L κ ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [jointMode, mode_at_zero] at h0

/-- **A joint mode is an eigenvector of the joint shift**, with eigenvalue `e^{−2πiΣκ/L}`. -/
theorem jointMode_shift (L : ℕ) {k : ℕ} (κ : Fin k → ℤ) :
    jointShift k (jointMode L κ) = Ring.root L (-(∑ i, κ i)) • jointMode L κ := by
  ext j
  change (∏ i, Ring.mode L (κ i) (j i - 1))
    = Ring.root L (-(∑ i, κ i)) * ∏ i, Ring.mode L (κ i) (j i)
  rw [show -(∑ i, κ i) = ∑ i, -κ i by rw [Finset.sum_neg_distrib], root_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h := Ring.shift_eigen L (κ i) (j i)
  unfold Ring.shift at h
  exact h

/-! ### Roots of unity and numbers modulo `L` -/

theorem root_mul_L (L : ℕ) (hL : 0 < L) (n : ℤ) : Ring.root L (n * L) = 1 := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : (2 * π * ((n * L : ℤ) : ℝ) / L : ℝ) = n * (2 * π) := by
    push_cast
    rw [show (2 * π * (↑n * ↑L) / ↑L : ℝ) = n * (2 * π) * (L / L) by ring, div_self hLr, mul_one]
  unfold Ring.root
  rw [e]
  have e' : (((n * (2 * π) : ℝ) : ℂ) * I) = (n : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [e', Complex.exp_int_mul_two_pi_mul_I]

theorem root_add_mul (L : ℕ) (hL : 0 < L) (a n : ℤ) :
    Ring.root L (a + n * L) = Ring.root L a := by
  rw [Ring.root_add, root_mul_L L hL, mul_one]

theorem root_emod (L : ℕ) (hL : 0 < L) (a : ℤ) : Ring.root L a = Ring.root L (a % L) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv a L]
  rw [mul_comm, root_add_mul L hL]

/-- **Equal roots of unity are equal numbers modulo `L`.** -/
theorem root_eq_iff (L : ℕ) (hL : 0 < L) (a b : ℤ) :
    Ring.root L a = Ring.root L b ↔ (a : ZMod L) = (b : ZMod L) := by
  rw [ZMod.intCast_eq_intCast_iff]
  have hLz : (0 : ℤ) < L := by exact_mod_cast hL
  constructor
  · intro h
    rw [root_emod L hL a, root_emod L hL b] at h
    exact Ring.root_injective L hL (Int.emod_nonneg a hLz.ne') (Int.emod_lt_of_pos a hLz)
      (Int.emod_nonneg b hLz.ne') (Int.emod_lt_of_pos b hLz) h
  · intro h
    have h' : a % L = b % L := h
    rw [root_emod L hL a, root_emod L hL b, h']

theorem root_neg_inj (L : ℕ) {a b : ℤ} (h : Ring.root L (-a) = Ring.root L (-b)) :
    Ring.root L a = Ring.root L b := by
  have ha := Ring.root_neg L a
  have hb := Ring.root_neg L b
  rw [eq_inv_of_mul_eq_one_left ha, eq_inv_of_mul_eq_one_left hb, h]

/-- **A uniform string carries no momentum** (Sec. IV): a mode that the shift leaves unchanged has
mode number `0` modulo `L`.  An empty ring holds a uniform string, so it carries no momentum until
a quantum enters it. -/
theorem uniform_mode_zero (L : ℕ) (hL : 0 < L) (κ : ℤ)
    (h : ∀ j, Ring.mode L κ (j - 1) = Ring.mode L κ j) : (κ : ZMod L) = 0 := by
  have h0 := h 0
  have e : Ring.mode L κ (0 - 1) = Ring.root L (-κ) * Ring.mode L κ 0 := Ring.shift_eigen L κ 0
  rw [h0, mode_at_zero, mul_one] at e
  have h1 : Ring.root L (-κ) = Ring.root L 0 := by
    rw [Ring.root_zero, ← e]
  have h2 := (root_eq_iff L hL (-κ) 0).1 h1
  push_cast at h2
  exact neg_eq_zero.1 h2

/-! ### Noether on `ℤ_L` -/

/-- **The total mode number is conserved modulo `L`** (Sec. IV).  A law `A` from the states of
`m` carriers to the states of `n` carriers that intertwines the joint shifts (no law depends on the
marks) sends the joint mode with numbers `κ` to an eigenvector of the joint shift with the same
eigenvalue; if that image is a multiple of the joint mode with numbers `κ'`, the two totals agree
modulo `L`. -/
theorem total_mode_conserved (L : ℕ) (hL : 0 < L) {m n : ℕ}
    (A : ((Fin m → ℤ) → ℂ) →ₗ[ℂ] ((Fin n → ℤ) → ℂ))
    (hA : A ∘ₗ jointShift m = jointShift n ∘ₗ A)
    (κ : Fin m → ℤ) (κ' : Fin n → ℤ) (c : ℂ) (hc : c ≠ 0)
    (h : A (jointMode L κ) = c • jointMode L κ') :
    ((∑ i, κ i : ℤ) : ZMod L) = ((∑ i, κ' i : ℤ) : ZMod L) := by
  have h1 : jointShift n (A (jointMode L κ))
      = Ring.root L (-(∑ i, κ i)) • A (jointMode L κ) := by
    have hc' := congrArg (fun T => T (jointMode L κ)) hA
    simp only [LinearMap.comp_apply] at hc'
    rw [← hc', jointMode_shift, map_smul]
  have h2 : jointShift n (A (jointMode L κ))
      = Ring.root L (-(∑ i, κ' i)) • A (jointMode L κ) := by
    rw [h, map_smul, jointMode_shift, smul_comm]
  have hne : A (jointMode L κ) ≠ 0 := by
    rw [h]
    exact smul_ne_zero hc (jointMode_ne_zero L κ')
  have heq : Ring.root L (-(∑ i, κ i)) = Ring.root L (-(∑ i, κ' i)) := by
    have h3 : (Ring.root L (-(∑ i, κ i)) - Ring.root L (-(∑ i, κ' i))) • A (jointMode L κ) = 0 := by
      rw [sub_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd h4 hne
  exact (root_eq_iff L hL _ _).1 (root_neg_inj L heq)

/-- **A vertex that intertwines the joint shifts exists**: `A f (j₀, j₁) = f(j₀) · mode_{κ₂}(j₁ − j₀)`
commutes with the joint shifts and takes the mode `κ` to the joint mode `(κ − κ₂, κ₂)`.  So the
hypotheses of `total_mode_conserved` and `three_leg_conservation` can be met. -/
theorem vertex_exists (L : ℕ) (κ κ2 : ℤ) :
    ∃ A : ((Fin 1 → ℤ) → ℂ) →ₗ[ℂ] ((Fin 2 → ℤ) → ℂ),
      A ∘ₗ jointShift 1 = jointShift 2 ∘ₗ A ∧
      A (jointMode L (fun _ => κ)) = (1 : ℂ) • jointMode L ![κ - κ2, κ2] := by
  refine ⟨{ toFun := fun f j => f (fun _ => j 0) * Ring.mode L κ2 (j 1 - j 0),
            map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro f g
    funext j
    simp [add_mul]
  · intro c f
    funext j
    simp [mul_assoc]
  · apply LinearMap.ext
    intro f
    funext j
    change f (fun _ => j 0 - 1) * Ring.mode L κ2 (j 1 - j 0)
      = f (fun _ => j 0 - 1) * Ring.mode L κ2 ((j 1 - 1) - (j 0 - 1))
    rw [show (j 1 - 1) - (j 0 - 1) = j 1 - j 0 by ring]
  · funext j
    change (jointMode L (fun _ => κ)) (fun _ => j 0) * Ring.mode L κ2 (j 1 - j 0)
      = ((1 : ℂ) • jointMode L ![κ - κ2, κ2]) j
    rw [one_smul]
    simp only [jointMode, Fin.prod_univ_one, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    unfold Ring.mode
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- **No wrap**: two numbers in the window `(−L/2, L/2]` that agree modulo `L` are equal. -/
theorem eq_of_window (L : ℕ) {a b : ℤ} (ha1 : -(L : ℤ) < 2 * a) (ha2 : 2 * a ≤ L)
    (hb1 : -(L : ℤ) < 2 * b) (hb2 : 2 * b ≤ L) (h : (a : ZMod L) = (b : ZMod L)) : a = b := by
  have hmod : a ≡ b [ZMOD L] := (ZMod.intCast_eq_intCast_iff _ _ _).1 h
  have hdvd : (L : ℤ) ∣ b - a := Int.ModEq.dvd hmod
  have habs : |b - a| < L := by
    rw [abs_lt]
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- **Conservation at the three-leg vertex** (Sec. IV): along every ring `u` through the cell the
vertex is a law from the state of the incoming string to the joint state of the two outgoing
strings that intertwines the joint shifts and takes the incoming mode to a multiple of the outgoing
joint mode; below the Planck momentum, `κ_in = κ_out,1 + κ_out,2` along every ring. -/
theorem three_leg_conservation (L : ℕ) (hL : 0 < L) {d : ℕ}
    (κin : Fin d → ℤ) (κout : Fin d → Fin 2 → ℤ)
    (A : Fin d → ((Fin 1 → ℤ) → ℂ) →ₗ[ℂ] ((Fin 2 → ℤ) → ℂ))
    (hA : ∀ u, A u ∘ₗ jointShift 1 = jointShift 2 ∘ₗ A u)
    (c : Fin d → ℂ) (hc : ∀ u, c u ≠ 0)
    (hmap : ∀ u, A u (jointMode L (fun _ => κin u)) = c u • jointMode L (κout u))
    (hwin : ∀ u, -(L : ℤ) < 2 * κin u ∧ 2 * κin u ≤ L ∧
      -(L : ℤ) < 2 * (κout u 0 + κout u 1) ∧ 2 * (κout u 0 + κout u 1) ≤ L) :
    ∀ u, κin u - κout u 0 - κout u 1 = 0 := by
  intro u
  have h := total_mode_conserved L hL (A u) (hA u) (fun _ => κin u) (κout u) (c u) (hc u) (hmap u)
  simp only [Fin.sum_univ_one, Fin.sum_univ_two] at h
  obtain ⟨h1, h2, h3, h4⟩ := hwin u
  have := eq_of_window L h1 h2 h3 h4 h
  omega

/-- **Conservation as vectors** (Sec. IV): if along every direction the mode numbers of the legs,
counted with their signs, sum to zero, the momenta sum to zero as vectors. -/
theorem sum_zero_of_components {k d : ℕ} (p : Fin k → Fin d → ℤ) (h : ∀ u, ∑ i, p i u = 0) :
    ∑ i, (fun u => (p i u : ℝ)) = (0 : Fin d → ℝ) := by
  ext u
  simp only [Finset.sum_apply, Pi.zero_apply]
  exact_mod_cast h u

end Conservation
end Register
