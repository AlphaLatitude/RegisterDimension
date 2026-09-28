import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cells of a sphere in `d` dimensions: Secs. V–VII of *The Dimension of Space from the
Granularity of Hilbert Space* (v16-29)

* `u_two_sphere`, `cos_sq_half_eq`: on the two-sphere the fraction of the area within polar angle
  `θ` of the pole is `u₁ = (1 − cos θ)/2`, Eq. (u), so `cos²(θ/2) = 1 − u₁` is Palmer's `m/L`.
* `band_area`: the `L` values of `u₁` cut the two-sphere into bands of equal area `4πR²/L`.
* `Gamma_two'`, `Gamma_three_halves`, `Gamma_five_halves`: the values of `Γ` the areas need.
* `Ω_two`, `Ω_three`, `Ω_four`, `Ω_five`: the area of the unit sphere, Eq. (omega), at
  `d = 2, 3, 4, 5`.
* `Npix_two`, `Npix_three`, `Npix_four`, `Npix_five`: the Planck-pixel count, Eq. (supply), at
  `d = 2, 3, 4, 5`: `L`, `L²/π`, `L³/4π`, `L⁴/6π²` (Table I).
* `C_two`, `C_three`, `C_four`: the ratio `C(d) = Ω_{d−1}/(2π)^{d−1}` of Eq. (C) is `1`, `1/π`,
  `1/4π`.
* `cell_area`: a cell of the grid on the horizon has area `ℓ_P²/π`, Eq. (cell), and
  `pixel_subtends_notch`: a Planck pixel subtends `2π/L`, one notch, on the horizon (Sec. VII).
-/

open Real

namespace Register
namespace Sphere

/-- **The area fraction on the two-sphere**, Eq. (u): `u₁(θ) = ∫₀^θ sin / ∫₀^π sin = (1 − cos θ)/2`. -/
theorem u_two_sphere (θ : ℝ) :
    (∫ x in (0 : ℝ)..θ, Real.sin x) / (∫ x in (0 : ℝ)..π, Real.sin x) = (1 - Real.cos θ) / 2 := by
  rw [integral_sin, integral_sin, Real.cos_zero, Real.cos_pi]
  norm_num

/-- **`cos²(θ/2) = 1 − u₁`** (Sec. V): the coordinate `u₁` of the grid is Palmer's, with
`cos²(θ/2)` the frequency `m/L`. -/
theorem cos_sq_half_eq (θ : ℝ) : Real.cos (θ / 2) ^ 2 = 1 - (1 - Real.cos θ) / 2 := by
  rw [Real.cos_sq, show 2 * (θ / 2) = θ by ring]
  ring

/-- **The `L` values of `u₁` cut the two-sphere into bands of equal area** (Sec. V): the band
between the latitudes at which `u₁ = m/L` and `u₁ = (m + 1)/L` has area `4πR²/L`. -/
theorem band_area (R L : ℝ) (m : ℕ) (θ₁ θ₂ : ℝ)
    (h₁ : (1 - Real.cos θ₁) / 2 = m / L) (h₂ : (1 - Real.cos θ₂) / 2 = (m + 1) / L) :
    2 * π * R ^ 2 * (Real.cos θ₁ - Real.cos θ₂) = 4 * π * R ^ 2 / L := by
  have e₁ : Real.cos θ₁ = 1 - 2 * (m / L) := by linarith
  have e₂ : Real.cos θ₂ = 1 - 2 * ((m + 1) / L) := by linarith
  rw [e₁, e₂]
  ring

lemma Gamma_two' : Real.Gamma 2 = 1 := by
  have h := Real.Gamma_add_one (s := (1 : ℝ)) one_ne_zero
  rw [Real.Gamma_one, mul_one] at h
  rw [show (2 : ℝ) = 1 + 1 by norm_num]
  exact h

lemma Gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
  have h := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  rw [Real.Gamma_one_half_eq] at h
  norm_num at h
  linarith

lemma Gamma_five_halves : Real.Gamma (5 / 2) = 3 * Real.sqrt π / 4 := by
  have h := Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num)
  rw [Gamma_three_halves] at h
  norm_num at h
  linarith

/-- the area of the unit sphere `S^{d−1}` in `d` dimensions, Eq. (omega), for real `d` -/
noncomputable def Ω (d : ℝ) : ℝ := 2 * π ^ (d / 2) / Real.Gamma (d / 2)

theorem Ω_two : Ω 2 = 2 * π := by
  unfold Ω
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, Real.Gamma_one, div_one]

theorem Ω_three : Ω 3 = 4 * π := by
  unfold Ω
  have h32 : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 pi_pos).ne'
  rw [h32, Real.rpow_add pi_pos, Real.rpow_one, ← Real.sqrt_eq_rpow, ← h32, Gamma_three_halves,
    show 2 * (π * Real.sqrt π) / (Real.sqrt π / 2) = 4 * π * (Real.sqrt π / Real.sqrt π) by ring,
    div_self hs, mul_one]

theorem Ω_four : Ω 4 = 2 * π ^ 2 := by
  unfold Ω
  rw [show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two, Gamma_two', div_one]

theorem Ω_five : Ω 5 = 8 * π ^ 2 / 3 := by
  unfold Ω
  have h52 : (5 : ℝ) / 2 = 2 + 1 / 2 := by norm_num
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 pi_pos).ne'
  rw [h52, Real.rpow_add pi_pos, Real.rpow_two, ← Real.sqrt_eq_rpow, ← h52, Gamma_five_halves,
    show 2 * (π ^ 2 * Real.sqrt π) / (3 * Real.sqrt π / 4)
      = 8 * π ^ 2 / 3 * (Real.sqrt π / Real.sqrt π) by ring,
    div_self hs, mul_one]

/-- the Planck pixels of the sphere, Eq. (supply): `N_pix(d) = Ω_{d−1} (L/2π)^{d−1}` -/
noncomputable def Npix (L d : ℝ) : ℝ := Ω d * (L / (2 * π)) ^ (d - 1)

theorem Npix_two (L : ℝ) : Npix L 2 = L := by
  unfold Npix
  rw [Ω_two, show (2 : ℝ) - 1 = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_one,
    show 2 * π * (L / (2 * π)) = L * (π / π) by ring, div_self pi_ne_zero, mul_one]

theorem Npix_three (L : ℝ) : Npix L 3 = L ^ 2 / π := by
  unfold Npix
  rw [Ω_three, show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show 4 * π * (L / (2 * π)) ^ 2 = L ^ 2 / π * (π / π) by ring, div_self pi_ne_zero, mul_one]

theorem Npix_four (L : ℝ) : Npix L 4 = L ^ 3 / (4 * π) := by
  unfold Npix
  rw [Ω_four, show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show 2 * π ^ 2 * (L / (2 * π)) ^ 3 = L ^ 3 / (4 * π) * (π / π) ^ 2 by ring,
    div_self pi_ne_zero, one_pow, mul_one]

theorem Npix_five (L : ℝ) : Npix L 5 = L ^ 4 / (6 * π ^ 2) := by
  unfold Npix
  rw [Ω_five, show (5 : ℝ) - 1 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show 8 * π ^ 2 / 3 * (L / (2 * π)) ^ 4 = L ^ 4 / (6 * π ^ 2) * (π / π) ^ 2 by ring,
    div_self pi_ne_zero, one_pow, mul_one]

/-- the ratio of Planck pixels to rational cells, Eq. (C): `C(d) = Ω_{d−1}/(2π)^{d−1}` -/
noncomputable def C (d : ℝ) : ℝ := Ω d / (2 * π) ^ (d - 1)

theorem C_two : C 2 = 1 := by
  unfold C
  rw [Ω_two, show (2 : ℝ) - 1 = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_one,
    div_self (by positivity)]

theorem C_three : C 3 = 1 / π := by
  unfold C
  rw [Ω_three, show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show 4 * π / (2 * π) ^ 2 = 1 / π * (π / π) by ring, div_self pi_ne_zero, mul_one]

theorem C_four : C 4 = 1 / (4 * π) := by
  unfold C
  rw [Ω_four, show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show 2 * π ^ 2 / (2 * π) ^ 3 = 1 / (4 * π) * (π / π) ^ 2 by ring, div_self pi_ne_zero,
    one_pow, mul_one]

/-- **A cell of the grid on the horizon has area `ℓ_P²/π`**, Eq. (cell): `4πR²/L²` with
`R = Lℓ_P/2π`. -/
theorem cell_area (L lP : ℝ) (hL : 0 < L) :
    4 * π * (L * lP / (2 * π)) ^ 2 / L ^ 2 = lP ^ 2 / π := by
  rw [show 4 * π * (L * lP / (2 * π)) ^ 2 / L ^ 2 = lP ^ 2 / π * (π / π) * (L / L) ^ 2 by ring,
    div_self pi_ne_zero, div_self hL.ne', one_pow, mul_one, mul_one]

/-- **A Planck pixel subtends one notch on the horizon** (Sec. VII): `√(4π/(L²/π)) = 2π/L`. -/
theorem pixel_subtends_notch (L : ℝ) (hL : 0 < L) :
    Real.sqrt (4 * π / (L ^ 2 / π)) = 2 * π / L := by
  have e : 4 * π / (L ^ 2 / π) = (2 * π / L) ^ 2 := by
    field_simp
    ring
  rw [e, Real.sqrt_sq (by positivity)]

end Sphere
end Register
