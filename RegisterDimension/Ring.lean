import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

/-!
# One ring: Secs. II–III of *The Dimension of Space from the Granularity of Hilbert Space* (v16-29)

The results that one ring of `L` cells gives, formalized on functions `ℤ → ℂ` that repeat after
`L` cells (a function on the ring).  Nothing is assumed beyond Postulate 1 read as: the shift `X`
moves every value one cell on, `(Xf)(j) = f(j − 1)`, that is `X|j⟩ = |j + 1⟩`, and the ring closes
after `L` cells.

* `born`: Born's rule as the half-angle identity, Eq. (raqm): with the mean outcome
  `cos θ = 2m/L − 1`, the frequency `m/L` of the outcome 1 is `cos²(θ/2)`.
* `phase_succ`: one notch is the step `2π/L` of phase.
* `mode_periodic`, `shift_mode`, `shift_eigen`: the mode with `κ` wavelengths around the ring is
  a function on the ring, moving one cell on multiplies it by the `L`th root of unity
  `e^{2πiκ/L}`, and it is an eigenfunction of the shift `X`, with eigenvalue `e^{−2πiκ/L}` in the
  convention `X|j⟩ = |j + 1⟩`: momentum along a ring is `κ` in quanta of `2πℏ/Lℓ_P`.
* `root_injective`: the `L` roots `κ = 0, …, L − 1` are distinct, so momentum along a ring takes
  exactly `L` values.
* `norm_mode`, `mode_uniform`: a mode has the same modulus at every cell, so it is found at every
  cell with probability `1/L`.
* `root_add`, `joint_mode`: for two strings the joint shift multiplies the product of modes by
  `e^{2πi(κ + κ')/L}`: mode numbers add.
* `weyl`: the clock `Z` and the shift `X` obey `ZX = e^{2πi/L} XZ`, the finite Weyl pair (Sec. X).
* `doublet_branches`, `doublet_mean`: the Dirac Hamiltonian on the ring, `H = cpσ_z + Mc²σ_x`, has
  the eigenvalues `±E` with `E² = p²c² + M²c⁴`, and on the positive branch the mean of `σ_z` is
  `cos θ = pc/E` (Sec. III).
-/

open Complex Real

namespace Register
namespace Ring

/-- the phase of a string at cyclic position `n`, Eq. (raqm): `φ = 2πn/L` -/
noncomputable def phase (L : ℕ) (n : ℤ) : ℝ := 2 * π * n / L

/-- **One notch is the step `2π/L` of phase** (Sec. II). -/
theorem phase_succ (L : ℕ) (n : ℤ) : phase L (n + 1) = phase L n + 2 * π / L := by
  unfold phase
  push_cast
  ring

/-- **Born's rule from the string** (Sec. II), Eq. (raqm): with the mean outcome
`cos θ = 2m/L − 1`, the frequency of the outcome 1 equals the squared amplitude, `cos²(θ/2) = m/L`. -/
theorem born (L m : ℕ) (θ : ℝ) (h : Real.cos θ = 2 * m / L - 1) :
    Real.cos (θ / 2) ^ 2 = m / L := by
  rw [Real.cos_sq, show 2 * (θ / 2) = θ by ring, h]
  ring

/-- the mode of number `κ`, the wave with `κ` wavelengths around the ring, at cell `j` -/
noncomputable def mode (L : ℕ) (κ j : ℤ) : ℂ :=
  Complex.exp (((2 * π * κ * j / L : ℝ) : ℂ) * I)

/-- the eigenvalue of the shift on the mode `κ`: the `L`th root of unity `e^{2πiκ/L}` -/
noncomputable def root (L : ℕ) (κ : ℤ) : ℂ :=
  Complex.exp (((2 * π * κ / L : ℝ) : ℂ) * I)

/-- **A mode is a function on the ring**: it repeats after `L` cells. -/
theorem mode_periodic (L : ℕ) (hL : 0 < L) (κ j : ℤ) : mode L κ (j + L) = mode L κ j := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : (2 * π * κ * ((j + L : ℤ) : ℝ) / L : ℝ) = 2 * π * κ * j / L + κ * (2 * π) := by
    push_cast
    rw [mul_add, add_div, mul_div_assoc (2 * π * (κ : ℝ)) (L : ℝ) (L : ℝ), div_self hLr, mul_one]
    ring
  unfold mode
  rw [e, Complex.ofReal_add, add_mul, Complex.exp_add]
  have h1 : Complex.exp (((κ * (2 * π) : ℝ) : ℂ) * I) = 1 := by
    have e' : (((κ * (2 * π) : ℝ) : ℂ) * I) = (κ : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [e', Complex.exp_int_mul_two_pi_mul_I]
  rw [h1, mul_one]

/-- **Moving one cell on multiplies a mode by a root of unity** (Sec. III): the value of the mode
`κ` at the next cell is `e^{2πiκ/L}` times its value here.  For the eigenvalue of the shift `X`
on the mode see `shift_eigen`. -/
theorem shift_mode (L : ℕ) (κ j : ℤ) : mode L κ (j + 1) = root L κ * mode L κ j := by
  have e : (2 * π * κ * ((j + 1 : ℤ) : ℝ) / L : ℝ) = 2 * π * κ / L + 2 * π * κ * j / L := by
    push_cast
    ring
  unfold mode root
  rw [e, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- **Roots multiply as their numbers add**: `e^{2πi(κ + κ')/L} = e^{2πiκ/L} e^{2πiκ'/L}`. -/
theorem root_add (L : ℕ) (κ κ' : ℤ) : root L (κ + κ') = root L κ * root L κ' := by
  have e : (2 * π * ((κ + κ' : ℤ) : ℝ) / L : ℝ) = 2 * π * κ / L + 2 * π * κ' / L := by
    push_cast
    ring
  unfold root
  rw [e, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- **Momentum along a ring takes `L` values** (Sec. III): the roots `κ = 0, …, L − 1` are
distinct. -/
theorem root_injective (L : ℕ) (hL : 0 < L) {κ κ' : ℤ} (h0 : 0 ≤ κ) (h1 : κ < L)
    (h0' : 0 ≤ κ') (h1' : κ' < L) (h : root L κ = root L κ') : κ = κ' := by
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold root at h
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have him := congrArg Complex.im hn
  simp at him
  -- him : 2πκ/L = 2πκ'/L + n·2π, up to the arrangement `simp` leaves
  have h2 : (2 * π * κ / L : ℝ) - 2 * π * κ' / L = n * (2 * π) := by linarith [him]
  have h3 : (2 * π * κ / L : ℝ) - 2 * π * κ' / L = (2 * π / L) * (κ - κ') := by ring
  have h5 : (2 * π / L : ℝ) * (n * L) = n * (2 * π) := by
    rw [show (2 * π / L : ℝ) * (n * L) = n * (2 * π) * (L / L) by ring, div_self hLr, mul_one]
  rw [h3, ← h5] at h2
  have h4 : (κ : ℝ) - κ' = n * L := mul_left_cancel₀ (by positivity) h2
  have keyZ : κ - κ' = n * L := by exact_mod_cast h4
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hlt | heq | hgt
    · have h' : n ≤ -1 := by omega
      have hL1 : (1 : ℤ) ≤ L := by omega
      nlinarith
    · exact heq
    · have h' : 1 ≤ n := by omega
      have hL1 : (1 : ℤ) ≤ L := by omega
      nlinarith
  rw [hn0] at keyZ
  simp at keyZ
  omega

/-- **A mode has modulus one at every cell.** -/
theorem norm_mode (L : ℕ) (κ j : ℤ) : ‖mode L κ j‖ = 1 := by
  unfold mode
  exact Complex.norm_exp_ofReal_mul_I _

/-- **A mode is found at every cell with the same probability, `1/L`** (Sec. III). -/
theorem mode_uniform (L : ℕ) (hL : 0 < L) (κ j : ℤ) :
    ‖mode L κ j / ((Real.sqrt L : ℝ) : ℂ)‖ ^ 2 = 1 / L := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [norm_div, norm_mode, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
    one_pow, Real.sq_sqrt hL'.le]

/-- **Mode numbers add** (Sec. IV, conservation): the joint shift of two strings multiplies the
product of their modes by `e^{2πi(κ + κ')/L}`. -/
theorem joint_mode (L : ℕ) (κ κ' j j' : ℤ) :
    mode L κ (j + 1) * mode L κ' (j' + 1) = root L (κ + κ') * (mode L κ j * mode L κ' j') := by
  rw [shift_mode, shift_mode, root_add]
  ring

/-- the shift `X` on functions on the ring: `(Xf)(j) = f(j − 1)`, that is `X|j⟩ = |j + 1⟩` -/
def shift (f : ℤ → ℂ) : ℤ → ℂ := fun j => f (j - 1)

/-- the clock `Z`: multiplies the value at cell `j` by `e^{2πij/L}` -/
noncomputable def clock (L : ℕ) (f : ℤ → ℂ) : ℤ → ℂ := fun j => root L j * f j

/-- `e^{2πi·0/L} = 1` -/
theorem root_zero (L : ℕ) : root L 0 = 1 := by
  unfold root
  simp

/-- the roots of `κ` and `−κ` are inverse to each other -/
theorem root_neg (L : ℕ) (κ : ℤ) : root L κ * root L (-κ) = 1 := by
  rw [← root_add, add_neg_cancel, root_zero]

/-- **A mode is an eigenfunction of the shift** (Sec. III): with `X|j⟩ = |j + 1⟩`, that is
`(Xf)(j) = f(j − 1)`, the shift multiplies the mode `κ` by `e^{−2πiκ/L}`; as `κ` runs over one
period these are the `L` roots of unity, the eigenvalues of `X`, and a state of definite momentum
is a mode. -/
theorem shift_eigen (L : ℕ) (κ j : ℤ) : shift (mode L κ) j = root L (-κ) * mode L κ j := by
  have h := shift_mode L κ (j - 1)
  rw [sub_add_cancel] at h
  unfold shift
  rw [h, ← mul_assoc, mul_comm (root L (-κ)) (root L κ), root_neg, one_mul]

/-- **The Weyl pair on a ring** (Sec. X): `ZX = e^{2πi/L} XZ`. -/
theorem weyl (L : ℕ) (f : ℤ → ℂ) (j : ℤ) :
    clock L (shift f) j = root L 1 * shift (clock L f) j := by
  have e : root L 1 * root L (j - 1) = root L j := by
    rw [← root_add]
    congr 1
    ring
  unfold clock shift
  rw [← e]
  ring

/-- **The two branches of the momentum doublet** (Sec. III).  The Dirac Hamiltonian on the ring,
`H = cpσ_z + Mc²σ_x = [[cp, Mc²], [Mc², −cp]]`, with `E² = p²c² + M²c⁴`, has the eigenvector
`(E + cp, Mc²)` with eigenvalue `E` and the eigenvector `(−Mc², E + cp)` with eigenvalue `−E`;
each conjunct is one row of `Hv = λv`. -/
theorem doublet_branches (c p M E : ℝ) (hE2 : E ^ 2 = c ^ 2 * p ^ 2 + M ^ 2 * c ^ 4) :
    (c * p * (E + c * p) + M * c ^ 2 * (M * c ^ 2) = E * (E + c * p) ∧
      M * c ^ 2 * (E + c * p) - c * p * (M * c ^ 2) = E * (M * c ^ 2)) ∧
    (c * p * (-(M * c ^ 2)) + M * c ^ 2 * (E + c * p) = -E * (-(M * c ^ 2)) ∧
      M * c ^ 2 * (-(M * c ^ 2)) - c * p * (E + c * p) = -E * (E + c * p)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linear_combination (-1 : ℝ) * hE2
  · ring
  · ring
  · linear_combination hE2

/-- **On the positive branch the mean outcome is `cos θ = pc/E`** (Sec. III): the mean of `σ_z` in
the eigenvector `(E + cp, Mc²)`. -/
theorem doublet_mean (c p M E : ℝ) (hE : 0 < E) (hE2 : E ^ 2 = c ^ 2 * p ^ 2 + M ^ 2 * c ^ 4)
    (hpos : 0 < E + c * p) :
    ((E + c * p) ^ 2 - (M * c ^ 2) ^ 2) / ((E + c * p) ^ 2 + (M * c ^ 2) ^ 2) = c * p / E := by
  have hsq : 0 < (E + c * p) ^ 2 := pow_pos hpos 2
  have hden : 0 < (E + c * p) ^ 2 + (M * c ^ 2) ^ 2 := by nlinarith [sq_nonneg (M * c ^ 2)]
  rw [div_eq_div_iff hden.ne' hE.ne']
  linear_combination (E + c * p) * hE2

end Ring
end Register
