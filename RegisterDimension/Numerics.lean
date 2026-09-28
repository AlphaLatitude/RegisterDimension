import RegisterDimension.Root
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# The numbers of *The Dimension of Space from the Granularity of Hilbert Space* (v16-29)

Every number quoted in the paper, certified as an interval from the paper's inputs.  The inputs are
the CODATA 2018 constants and the Planck 2018 cosmological parameters the paper uses:
`c = 299 792 458 m/s`, `ℏ = 1.054 571 817 × 10⁻³⁴ J s`, `G = 6.674 30 × 10⁻¹¹ m³ kg⁻¹ s⁻²`,
`H₀ = 67.4 km/s/Mpc`, `Ω_Λ = 0.685`; and the paper's rounded register length `L₀ = 6.4 × 10⁶¹`.
Every bound on `π`, `ln 2`, `e` is Mathlib's; the bounds on `ln L₀`, `ln π` and `ln 10` are derived
here from `e^x < 1/(1 − x)` and `1 + x ≤ e^x` raised to a power.

* `Lval_bounds`: `L = 2πR_L/ℓ_P` from the inputs lies in `(6.446, 6.447) × 10⁶¹` (the paper: `6.4 × 10⁶¹`).
* `mom_count`: `L₀² = 4.096 × 10¹²³` (the paper: `4.10 × 10¹²³`).
* `Npix_three_val`, `Npix_four_val`, `Npix_five_val`: Table I, `1.30 × 10¹²³`, `2.09 × 10¹⁸⁴`,
  `2.83 × 10²⁴⁵`; `ratios_val`: `L/4π = 5.1 × 10⁶⁰`, `4π/L = 2.0 × 10⁻⁶¹`, `6π²/L² = 1.4 × 10⁻¹²²`.
* `horizon_units`: `L²/4π = 3.3 × 10¹²²` (Sec. VII).
* `capacity_205`, `nmax_205`, `bits`, `bits_three`, `bits_area`: `205` bits per string,
  `616` bits of position, `409` bits of horizon area (Sec. VII).
* `ang_mom_val`: `ℏL/2 = 3.4 × 10²⁷ J s` (Sec. VIII).
* `log_L0_bounds`, `log_pi_bounds`, `log_ten_bounds`: `ln L₀ ∈ (142.3138, 142.3142)`,
  `ln π ∈ (1.1447, 1.1448)`, `ln 10 ∈ (2.302, 2.3032)`.
* `leading_term`, `bound_value`, `pixel_choice`: `3 + ln π/ln L = 3.0080`, `ln 4π/ln L = 0.018`,
  `ln 4/ln L = 0.010` (Sec. VI).
* `root_at_L0`: the root of the relaxed count at `L₀` lies in `(3.00810, 3.00813)`: `3.0081`, and
  it is the only solution below `L₀²/2π` (the paper's `3.008117` is a numerical evaluation, not
  certified beyond these four decimals).
* `factor_of_ten`: the roots at `10L₀` and `L₀/10` lie within `2 × 10⁻⁴` of the root at `L₀`.
* `pixel_shift_val`: dividing the count by `4` moves the root up by between `0.0097` and `0.0099`.
* `seven_halves_factor_val`, `five_halves_factor_val`: the factor that puts the root at `7/2`
  lies in `(1.27, 1.44) × 10³⁰`; the one that puts it at `5/2` lies in `(1.13, 1.42) × 10³¹`.
-/

set_option exponentiation.threshold 50000

open Real Set

namespace Register
namespace DimensionNumerics

/-- the speed of light, exact -/
local notation "c₀" => (299792458 : ℝ)
/-- the reduced Planck constant, exact -/
local notation "ℏ₀" => (1054571817 : ℝ) / 10 ^ 43
/-- Newton's constant, CODATA 2018 -/
local notation "G₀" => (667430 : ℝ) / 10 ^ 16
/-- the Hubble constant, Planck 2018: `67.4 km/s/Mpc` in `1/s` -/
local notation "H₀" => (67400 : ℝ) / (30856775814913673 * 10 ^ 6)
/-- the dark-energy fraction, Planck 2018 -/
local notation "ΩΛ₀" => (685 : ℝ) / 1000
/-- the paper's rounded register length, `6.4 × 10⁶¹` -/
local notation "L₀" => (64 : ℝ) * 10 ^ 60

lemma pi_lo : (3.141592 : ℝ) < π := Real.pi_gt_d6
lemma pi_hi : π < (3.141593 : ℝ) := Real.pi_lt_d6
lemma pi_sq_lo : (3.141592 : ℝ) ^ 2 < π ^ 2 := pow_lt_pow_left₀ pi_lo (by norm_num) (by norm_num)
lemma pi_sq_hi : π ^ 2 < (3.141593 : ℝ) ^ 2 := pow_lt_pow_left₀ pi_hi pi_pos.le (by norm_num)

lemma four_pi_lt_L0 : 4 * π < L₀ := by linarith [pi_hi]

/-! ### The register length from the inputs -/

/-- the de Sitter radius `R_L = c/(H₀√Ω_Λ)` -/
noncomputable def RL : ℝ := c₀ / (H₀ * Real.sqrt ΩΛ₀)
/-- the Planck length `ℓ_P = √(ℏG/c³)` -/
noncomputable def lP : ℝ := Real.sqrt (ℏ₀ * G₀ / c₀ ^ 3)
/-- the register length, `L = 2πR_L/ℓ_P` -/
noncomputable def Lval : ℝ := 2 * π * RL / lP

lemma Lval_sq : Lval ^ 2 = π ^ 2 * (4 * c₀ ^ 5 / (H₀ ^ 2 * ΩΛ₀ * ℏ₀ * G₀)) := by
  have h1 : Real.sqrt ΩΛ₀ ^ 2 = ΩΛ₀ := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt (ℏ₀ * G₀ / c₀ ^ 3) ^ 2 = ℏ₀ * G₀ / c₀ ^ 3 := Real.sq_sqrt (by positivity)
  unfold Lval RL lP
  simp only [div_pow, mul_pow]
  rw [h1, h2]
  ring

lemma Lval_pos : 0 < Lval := by
  unfold Lval RL lP
  positivity

/-- **The register length from the inputs**: `6.446 × 10⁶¹ < L < 6.447 × 10⁶¹`; the paper rounds
to `6.4 × 10⁶¹`. -/
theorem Lval_bounds : (6.446 : ℝ) * 10 ^ 61 < Lval ∧ Lval < 6.447 * 10 ^ 61 := by
  have hpos := Lval_pos
  constructor
  · have h : ((6.446 : ℝ) * 10 ^ 61) ^ 2 < Lval ^ 2 := by
      rw [Lval_sq]
      calc ((6.446 : ℝ) * 10 ^ 61) ^ 2
          < (3.141592 : ℝ) ^ 2 * (4 * c₀ ^ 5 / (H₀ ^ 2 * ΩΛ₀ * ℏ₀ * G₀)) := by norm_num
        _ < π ^ 2 * (4 * c₀ ^ 5 / (H₀ ^ 2 * ΩΛ₀ * ℏ₀ * G₀)) :=
            mul_lt_mul_of_pos_right pi_sq_lo (by norm_num)
    exact (pow_lt_pow_iff_left₀ (by norm_num) hpos.le (by norm_num)).1 h
  · have h : Lval ^ 2 < ((6.447 : ℝ) * 10 ^ 61) ^ 2 := by
      rw [Lval_sq]
      calc π ^ 2 * (4 * c₀ ^ 5 / (H₀ ^ 2 * ΩΛ₀ * ℏ₀ * G₀))
          < (3.141593 : ℝ) ^ 2 * (4 * c₀ ^ 5 / (H₀ ^ 2 * ΩΛ₀ * ℏ₀ * G₀)) :=
            mul_lt_mul_of_pos_right pi_sq_hi (by norm_num)
        _ < ((6.447 : ℝ) * 10 ^ 61) ^ 2 := by norm_num
    exact (pow_lt_pow_iff_left₀ hpos.le (by norm_num) (by norm_num)).1 h

/-! ### The counts of Table I and Secs. IV, VII, VIII -/

/-- **`L₀² = 4.096 × 10¹²³`** momenta of one string, the paper's `4.10 × 10¹²³` (Sec. IV). -/
theorem mom_count : L₀ ^ 2 = 4.096 * 10 ^ 123 := by norm_num

/-- **`N_pix(3) = L₀²/π = 1.30 × 10¹²³`** (Table I). -/
theorem Npix_three_val :
    (1.303 : ℝ) * 10 ^ 123 < Sphere.Npix L₀ 3 ∧ Sphere.Npix L₀ 3 < 1.304 * 10 ^ 123 := by
  rw [Sphere.Npix_three]
  constructor
  · rw [lt_div_iff₀ pi_pos]
    calc (1.303 : ℝ) * 10 ^ 123 * π < 1.303 * 10 ^ 123 * 3.141593 :=
          mul_lt_mul_of_pos_left pi_hi (by norm_num)
      _ < L₀ ^ 2 := by norm_num
  · rw [div_lt_iff₀ pi_pos]
    calc L₀ ^ 2 < (1.304 : ℝ) * 10 ^ 123 * 3.141592 := by norm_num
      _ < 1.304 * 10 ^ 123 * π := mul_lt_mul_of_pos_left pi_lo (by norm_num)

/-- **`N_pix(4) = L₀³/4π = 2.09 × 10¹⁸⁴`** (Table I). -/
theorem Npix_four_val :
    (2.086 : ℝ) * 10 ^ 184 < Sphere.Npix L₀ 4 ∧ Sphere.Npix L₀ 4 < 2.087 * 10 ^ 184 := by
  rw [Sphere.Npix_four]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    calc (2.086 : ℝ) * 10 ^ 184 * (4 * π) < 2.086 * 10 ^ 184 * (4 * 3.141593) :=
          mul_lt_mul_of_pos_left (by linarith [pi_hi]) (by norm_num)
      _ < L₀ ^ 3 := by norm_num
  · rw [div_lt_iff₀ (by positivity)]
    calc L₀ ^ 3 < (2.087 : ℝ) * 10 ^ 184 * (4 * 3.141592) := by norm_num
      _ < 2.087 * 10 ^ 184 * (4 * π) := mul_lt_mul_of_pos_left (by linarith [pi_lo]) (by norm_num)

/-- **`N_pix(5) = L₀⁴/6π² = 2.83 × 10²⁴⁵`** (Table I). -/
theorem Npix_five_val :
    (2.833 : ℝ) * 10 ^ 245 < Sphere.Npix L₀ 5 ∧ Sphere.Npix L₀ 5 < 2.834 * 10 ^ 245 := by
  rw [Sphere.Npix_five]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    calc (2.833 : ℝ) * 10 ^ 245 * (6 * π ^ 2) < 2.833 * 10 ^ 245 * (6 * 3.141593 ^ 2) :=
          mul_lt_mul_of_pos_left (by linarith [pi_sq_hi]) (by norm_num)
      _ < L₀ ^ 4 := by norm_num
  · rw [div_lt_iff₀ (by positivity)]
    calc L₀ ^ 4 < (2.834 : ℝ) * 10 ^ 245 * (6 * 3.141592 ^ 2) := by norm_num
      _ < 2.834 * 10 ^ 245 * (6 * π ^ 2) :=
          mul_lt_mul_of_pos_left (by linarith [pi_sq_lo]) (by norm_num)

/-- **The ratios of Table I**: `L/4π = 5.1 × 10⁶⁰`, `4π/L = 2.0 × 10⁻⁶¹`, `6π²/L² = 1.4 × 10⁻¹²²`,
and the ratio `π` of the counts at `d = 3` and `d = 2` is `3.14`. -/
theorem ratios_val :
    ((5.09 : ℝ) * 10 ^ 60 < L₀ / (4 * π) ∧ L₀ / (4 * π) < 5.10 * 10 ^ 60) ∧
    ((1.96 : ℝ) / 10 ^ 61 < 4 * π / L₀ ∧ 4 * π / L₀ < 1.97 / 10 ^ 61) ∧
    ((1.44 : ℝ) / 10 ^ 122 < 6 * π ^ 2 / L₀ ^ 2 ∧ 6 * π ^ 2 / L₀ ^ 2 < 1.45 / 10 ^ 122) ∧
    ((3.14 : ℝ) < π ∧ π < 3.142) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]
    calc (5.09 : ℝ) * 10 ^ 60 * (4 * π) < 5.09 * 10 ^ 60 * (4 * 3.141593) :=
          mul_lt_mul_of_pos_left (by linarith [pi_hi]) (by norm_num)
      _ < L₀ := by norm_num
  · rw [div_lt_iff₀ (by positivity)]
    calc L₀ < (5.10 : ℝ) * 10 ^ 60 * (4 * 3.141592) := by norm_num
      _ < 5.10 * 10 ^ 60 * (4 * π) := mul_lt_mul_of_pos_left (by linarith [pi_lo]) (by norm_num)
  · rw [lt_div_iff₀ (by positivity)]
    calc (1.96 : ℝ) / 10 ^ 61 * L₀ < 4 * 3.141592 := by norm_num
      _ < 4 * π := by linarith [pi_lo]
  · rw [div_lt_iff₀ (by positivity)]
    calc 4 * π < 4 * 3.141593 := by linarith [pi_hi]
      _ < (1.97 : ℝ) / 10 ^ 61 * L₀ := by norm_num
  · rw [lt_div_iff₀ (by positivity)]
    calc (1.44 : ℝ) / 10 ^ 122 * L₀ ^ 2 < 6 * 3.141592 ^ 2 := by norm_num
      _ < 6 * π ^ 2 := by linarith [pi_sq_lo]
  · rw [div_lt_iff₀ (by positivity)]
    calc 6 * π ^ 2 < 6 * 3.141593 ^ 2 := by linarith [pi_sq_hi]
      _ < (1.45 : ℝ) / 10 ^ 122 * L₀ ^ 2 := by norm_num
  · linarith [pi_lo]
  · linarith [pi_hi]

/-- **`1/π = 0.318`**: the cell of the horizon grid is `ℓ_P²/π = 0.318 ℓ_P²` (Sec. VII). -/
theorem inv_pi_val : (0.3183 : ℝ) < 1 / π ∧ 1 / π < 0.3184 := by
  constructor
  · rw [lt_div_iff₀ pi_pos]
    linarith [pi_hi]
  · rw [div_lt_iff₀ pi_pos]
    linarith [pi_lo]

/-- **The horizon holds `L₀²/4π = 3.3 × 10¹²²` Planck units of area** (Sec. VII). -/
theorem horizon_units :
    (3.25 : ℝ) * 10 ^ 122 < L₀ ^ 2 / (4 * π) ∧ L₀ ^ 2 / (4 * π) < 3.26 * 10 ^ 122 := by
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    calc (3.25 : ℝ) * 10 ^ 122 * (4 * π) < 3.25 * 10 ^ 122 * (4 * 3.141593) :=
          mul_lt_mul_of_pos_left (by linarith [pi_hi]) (by norm_num)
      _ < L₀ ^ 2 := by norm_num
  · rw [div_lt_iff₀ (by positivity)]
    calc L₀ ^ 2 < (3.26 : ℝ) * 10 ^ 122 * (4 * 3.141592) := by norm_num
      _ < 3.26 * 10 ^ 122 * (4 * π) := mul_lt_mul_of_pos_left (by linarith [pi_lo]) (by norm_num)

/-- the range on which the relaxed count has one solution, `L₀²/2π = 6.5 × 10¹²²` -/
theorem uniqueness_range :
    (6.5 : ℝ) * 10 ^ 122 < L₀ ^ 2 / (2 * π) ∧ L₀ ^ 2 / (2 * π) < 6.52 * 10 ^ 122 := by
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    calc (6.5 : ℝ) * 10 ^ 122 * (2 * π) < 6.5 * 10 ^ 122 * (2 * 3.141593) :=
          mul_lt_mul_of_pos_left (by linarith [pi_hi]) (by norm_num)
      _ < L₀ ^ 2 := by norm_num
  · rw [div_lt_iff₀ (by positivity)]
    calc L₀ ^ 2 < (6.52 : ℝ) * 10 ^ 122 * (2 * 3.141592) := by norm_num
      _ < 6.52 * 10 ^ 122 * (2 * π) := mul_lt_mul_of_pos_left (by linarith [pi_lo]) (by norm_num)

/-- **`ℏL₀/2 = 3.4 × 10²⁷ J s`**, the largest angular momentum of one string (Sec. VIII). -/
theorem ang_mom_val : (3.37 : ℝ) * 10 ^ 27 < ℏ₀ * L₀ / 2 ∧ ℏ₀ * L₀ / 2 < 3.38 * 10 ^ 27 := by
  constructor <;> norm_num

/-- **`2²⁰⁵ < L₀ < 2²⁰⁶`**: a string is `205` bits (Sec. VII). -/
theorem capacity_205 : (2 : ℝ) ^ 205 < L₀ ∧ L₀ < 2 ^ 206 := by
  constructor <;> norm_num

/-- **`2^N ≤ L₀` exactly when `N ≤ 205`**: `205` bits fit in a string and `206` do not. -/
theorem nmax_205 (N : ℕ) : (2 : ℝ) ^ N ≤ L₀ ↔ N ≤ 205 := by
  constructor
  · intro h
    by_contra hN
    have h206 : 206 ≤ N := by omega
    have : (2 : ℝ) ^ 206 ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) h206
    have := capacity_205.2
    linarith
  · intro h
    have : (2 : ℝ) ^ N ≤ 2 ^ 205 := pow_le_pow_right₀ (by norm_num) h
    have := capacity_205.1
    linarith

/-! ### Logarithms: `ln L₀`, `ln π`, `ln 10` -/

/-- **`ln L₀ ∈ (142.3138, 142.3142)`**: `L₀ = 2²⁰⁵ r` with `e^{0.2187} < r < e^{0.2190}`. -/
theorem log_L0_bounds : (142.3138 : ℝ) < Real.log L₀ ∧ Real.log L₀ < 142.3142 := by
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  have hx1 : Real.exp (0.2187 / 256) < 1 / (1 - 0.2187 / 256) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have hx2 : (0.2190 / 256 : ℝ) + 1 ≤ Real.exp (0.2190 / 256) := Real.add_one_le_exp _
  have e1 : Real.exp 0.2187 = Real.exp (0.2187 / 256) ^ 256 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have e2 : Real.exp 0.2190 = Real.exp (0.2190 / 256) ^ 256 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have h1 : Real.exp 0.2187 < L₀ / 2 ^ 205 := by
    rw [e1]
    calc Real.exp (0.2187 / 256) ^ 256 < (1 / (1 - 0.2187 / 256)) ^ 256 :=
          pow_lt_pow_left₀ hx1 (Real.exp_pos _).le (by norm_num)
      _ < L₀ / 2 ^ 205 := by norm_num
  have h2 : L₀ / 2 ^ 205 < Real.exp 0.2190 := by
    rw [e2]
    calc L₀ / 2 ^ 205 < ((0.2190 / 256 : ℝ) + 1) ^ 256 := by norm_num
      _ ≤ Real.exp (0.2190 / 256) ^ 256 := pow_le_pow_left₀ (by norm_num) hx2 256
  have hlog1 : (0.2187 : ℝ) < Real.log (L₀ / 2 ^ 205) := by
    have := Real.log_lt_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hlog2 : Real.log (L₀ / 2 ^ 205) < 0.2190 := by
    have := Real.log_lt_log (by norm_num) h2
    rwa [Real.log_exp] at this
  have hsplit : Real.log L₀ = 205 * Real.log 2 + Real.log (L₀ / 2 ^ 205) := by
    have e : (2 : ℝ) ^ 205 * (L₀ / 2 ^ 205) = L₀ := by norm_num
    have h := Real.log_mul (show (2 : ℝ) ^ 205 ≠ 0 by norm_num)
      (show L₀ / 2 ^ 205 ≠ 0 by norm_num)
    rw [e, Real.log_pow] at h
    push_cast at h
    linarith
  rw [hsplit]
  constructor <;> linarith

/-- **`ln π ∈ (1.1447, 1.1448)`**: `e^{1.1447} < 3.141592 < π < 3.141593 < e^{1.1448}`. -/
theorem log_pi_bounds : (1.1447 : ℝ) < Real.log π ∧ Real.log π < 1.1448 := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hx1 : Real.exp (0.1447 / 512) < 1 / (1 - 0.1447 / 512) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have hx2 : (0.1448 / 1024 : ℝ) + 1 ≤ Real.exp (0.1448 / 1024) := Real.add_one_le_exp _
  have e1 : Real.exp 1.1447 = Real.exp 1 * Real.exp (0.1447 / 512) ^ 512 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  have e2 : Real.exp 1.1448 = Real.exp 1 * Real.exp (0.1448 / 1024) ^ 1024 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  constructor
  · have h : Real.exp 1.1447 < π := by
      rw [e1]
      calc Real.exp 1 * Real.exp (0.1447 / 512) ^ 512
          < 2.7182818286 * (1 / (1 - 0.1447 / 512)) ^ 512 :=
            mul_lt_mul'' he2 (pow_lt_pow_left₀ hx1 (Real.exp_pos _).le (by norm_num))
              (Real.exp_pos _).le (by positivity)
        _ < 3.141592 := by norm_num
        _ < π := pi_lo
    have := Real.log_lt_log (Real.exp_pos _) h
    rwa [Real.log_exp] at this
  · have h : π < Real.exp 1.1448 := by
      rw [e2]
      calc π < 3.141593 := pi_hi
        _ < 2.7182818283 * ((0.1448 / 1024 : ℝ) + 1) ^ 1024 := by norm_num
        _ ≤ Real.exp 1 * Real.exp (0.1448 / 1024) ^ 1024 :=
            mul_le_mul he1.le (pow_le_pow_left₀ (by norm_num) hx2 1024) (by positivity)
              (Real.exp_pos _).le
    have := Real.log_lt_log pi_pos h
    rwa [Real.log_exp] at this

/-- **`ln 10 ∈ (2.302, 2.3032)`**: `e^{2.302} < 10 < e^{2.3032}`. -/
theorem log_ten_bounds : (2.302 : ℝ) < Real.log 10 ∧ Real.log 10 < 2.3032 := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hx1 : Real.exp (0.302 / 128) < 1 / (1 - 0.302 / 128) :=
    Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
  have hx2 : (0.3032 / 128 : ℝ) + 1 ≤ Real.exp (0.3032 / 128) := Real.add_one_le_exp _
  have e1 : Real.exp 2.302 = Real.exp 1 ^ 2 * Real.exp (0.302 / 128) ^ 128 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  have e2 : Real.exp 2.3032 = Real.exp 1 ^ 2 * Real.exp (0.3032 / 128) ^ 128 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  have hesq1 : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 :=
    pow_lt_pow_left₀ he2 (Real.exp_pos _).le (by norm_num)
  have hesq2 : (2.7182818283 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
    pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
  constructor
  · have h : Real.exp 2.302 < 10 := by
      rw [e1]
      calc Real.exp 1 ^ 2 * Real.exp (0.302 / 128) ^ 128
          < 2.7182818286 ^ 2 * (1 / (1 - 0.302 / 128)) ^ 128 :=
            mul_lt_mul'' hesq1 (pow_lt_pow_left₀ hx1 (Real.exp_pos _).le (by norm_num))
              (by positivity) (by positivity)
        _ < 10 := by norm_num
    have := Real.log_lt_log (Real.exp_pos _) h
    rwa [Real.log_exp] at this
  · have h : (10 : ℝ) < Real.exp 2.3032 := by
      rw [e2]
      calc (10 : ℝ) < 2.7182818283 ^ 2 * ((0.3032 / 128 : ℝ) + 1) ^ 128 := by norm_num
        _ ≤ Real.exp 1 ^ 2 * Real.exp (0.3032 / 128) ^ 128 :=
            mul_le_mul hesq2.le (pow_le_pow_left₀ (by norm_num) hx2 128) (by positivity)
              (by positivity)
    have := Real.log_lt_log (by norm_num) h
    rwa [Real.log_exp] at this

/-! ### Bits -/

/-- **`log₂ L₀ = 205.3`**: a string holds `205` bits (Sec. VII). -/
theorem bits : (205.31 : ℝ) < Real.logb 2 L₀ ∧ Real.logb 2 L₀ < 205.32 := by
  obtain ⟨h1, h2⟩ := log_L0_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  unfold Real.logb
  constructor
  · rw [lt_div_iff₀ Root.log_two_pos]
    nlinarith
  · rw [div_lt_iff₀ Root.log_two_pos]
    nlinarith

/-- **`3 log₂ L₀ = 616` bits of position** (Sec. VII). -/
theorem bits_three : (615.5 : ℝ) < 3 * Real.logb 2 L₀ ∧ 3 * Real.logb 2 L₀ < 616.5 := by
  obtain ⟨h1, h2⟩ := bits
  constructor <;> linarith

/-- **`log₂(L₀²/π) = 409` bits of horizon area** (Sec. VII). -/
theorem bits_area :
    (408.5 : ℝ) < Real.logb 2 (L₀ ^ 2 / π) ∧ Real.logb 2 (L₀ ^ 2 / π) < 409.5 := by
  obtain ⟨h1, h2⟩ := log_L0_bounds
  obtain ⟨hp1, hp2⟩ := log_pi_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  unfold Real.logb
  rw [Real.log_div (by positivity) pi_pos.ne', Real.log_pow]
  push_cast
  constructor
  · rw [lt_div_iff₀ Root.log_two_pos]
    nlinarith
  · rw [div_lt_iff₀ Root.log_two_pos]
    nlinarith

/-! ### The relaxed count at `L₀` -/

/-- **`3 + ln π/ln L₀ = 3.0080`**, the leading term of the root (Sec. VI). -/
theorem leading_term :
    (3.00804 : ℝ) < 3 + Real.log π / Real.log L₀ ∧ 3 + Real.log π / Real.log L₀ < 3.00805 := by
  obtain ⟨h1, h2⟩ := log_L0_bounds
  obtain ⟨hp1, hp2⟩ := log_pi_bounds
  have hL0 : 0 < Real.log L₀ := lt_trans (by norm_num) h1
  have a : (0.00804 : ℝ) < Real.log π / Real.log L₀ := by
    rw [lt_div_iff₀ hL0]
    nlinarith
  have b : Real.log π / Real.log L₀ < 0.00805 := by
    rw [div_lt_iff₀ hL0]
    nlinarith
  constructor <;> linarith

/-- **`ln 4π/ln L₀ = 0.018`**, the bound of Eq. (bound) (Sec. VI). -/
theorem bound_value :
    (0.0177 : ℝ) < Real.log (4 * π) / Real.log L₀ ∧ Real.log (4 * π) / Real.log L₀ < 0.0178 := by
  obtain ⟨h1, h2⟩ := log_L0_bounds
  obtain ⟨hp1, hp2⟩ := log_pi_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  have hL0 : 0 < Real.log L₀ := lt_trans (by norm_num) h1
  rw [Root.log_four_pi]
  constructor
  · rw [lt_div_iff₀ hL0]
    nlinarith
  · rw [div_lt_iff₀ hL0]
    nlinarith

/-- **`ln 4/ln L₀ = 0.010`**: the shift of the root for pixels of side `2ℓ_P` (Sec. VI). -/
theorem pixel_choice :
    (0.00974 : ℝ) < Real.log 4 / Real.log L₀ ∧ Real.log 4 / Real.log L₀ < 0.00975 := by
  obtain ⟨h1, h2⟩ := log_L0_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  have hL0 : 0 < Real.log L₀ := lt_trans (by norm_num) h1
  rw [Root.log_four]
  constructor
  · rw [lt_div_iff₀ hL0]
    nlinarith
  · rw [div_lt_iff₀ hL0]
    nlinarith

/-- the bracket of Sec. VI at `L₀`: `η₁ ≥ 0.0081086` and `η₂ ≤ 0.0081235` -/
lemma eta_L0 :
    (0.0081086 : ℝ) ≤ Real.log π / (Real.log L₀ - Real.log π) ∧
      Real.log π / (Real.log L₀ - Real.log 4) ≤ 0.0081235 := by
  obtain ⟨h1, h2⟩ := log_L0_bounds
  obtain ⟨hp1, hp2⟩ := log_pi_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  rw [Root.log_four]
  constructor
  · rw [le_div_iff₀ (by set A := Real.log L₀ with hA; linarith)]
    nlinarith
  · rw [div_le_iff₀ (by set A := Real.log L₀ with hA; linarith)]
    nlinarith

/-- **The root of the relaxed count at `L₀` is `3.0081`, and it is the only root below
`L₀²/2π`** (Sec. VI): it lies in `(3.00810, 3.00813)`. -/
theorem root_at_L0 :
    ∃ d ∈ Icc (2 : ℝ) 4, Root.g L₀ d = 0 ∧ (3.00810 : ℝ) < d ∧ d < 3.00813 ∧
      ∀ d', 0 < d' → d' < L₀ ^ 2 / (2 * π) → Root.g L₀ d' = 0 → d' = d := by
  obtain ⟨d, hd, hg, -, ⟨hb1, hb2⟩, huniq⟩ := Root.unique_root L₀ four_pi_lt_L0
  obtain ⟨e1, e2⟩ := eta_L0
  exact ⟨d, hd, hg, by linarith, by linarith, huniq⟩

/-- the bracket at `10 L₀` -/
lemma eta_10L0 :
    (0.0079785 : ℝ) ≤ Real.log π / (Real.log (10 * L₀) - Real.log π) ∧
      Real.log π / (Real.log (10 * L₀) - Real.log 4) ≤ 0.007993 := by
  obtain ⟨h1, h2⟩ := log_L0_bounds
  obtain ⟨hp1, hp2⟩ := log_pi_bounds
  obtain ⟨ht1, ht2⟩ := log_ten_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  rw [Root.log_four, Real.log_mul (by norm_num) (by norm_num)]
  constructor
  · rw [le_div_iff₀ (by set A := Real.log L₀ with hA; linarith)]
    nlinarith
  · rw [div_le_iff₀ (by set A := Real.log L₀ with hA; linarith)]
    nlinarith

/-- the bracket at `L₀/10` -/
lemma eta_L0_10 :
    (0.008243 : ℝ) ≤ Real.log π / (Real.log (L₀ / 10) - Real.log π) ∧
      Real.log π / (Real.log (L₀ / 10) - Real.log 4) ≤ 0.008259 := by
  obtain ⟨h1, h2⟩ := log_L0_bounds
  obtain ⟨hp1, hp2⟩ := log_pi_bounds
  obtain ⟨ht1, ht2⟩ := log_ten_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  rw [Root.log_four, Real.log_div (by norm_num) (by norm_num)]
  constructor
  · rw [le_div_iff₀ (by set A := Real.log L₀ with hA; linarith)]
    nlinarith
  · rw [div_le_iff₀ (by set A := Real.log L₀ with hA; linarith)]
    nlinarith

/-- **A factor of ten in `L` moves the root by less than `2 × 10⁻⁴`** (Sec. VI): the roots at
`10L₀` and `L₀/10` lie within `2 × 10⁻⁴` of the root at `L₀`. -/
theorem factor_of_ten {d₀ d₁ d₂ : ℝ}
    (h₀ : d₀ ∈ Icc (2 : ℝ) 4) (hg₀ : Root.g L₀ d₀ = 0)
    (h₁ : d₁ ∈ Icc (2 : ℝ) 4) (hg₁ : Root.g (10 * L₀) d₁ = 0)
    (h₂ : d₂ ∈ Icc (2 : ℝ) 4) (hg₂ : Root.g (L₀ / 10) d₂ = 0) :
    |d₁ - d₀| < 2 / 10 ^ 4 ∧ |d₂ - d₀| < 2 / 10 ^ 4 := by
  have hL1 : 4 * π < 10 * L₀ := by linarith [pi_hi]
  have hL2 : 4 * π < L₀ / 10 := by linarith [pi_hi]
  obtain ⟨a0, b0⟩ := Root.root_bracket L₀ four_pi_lt_L0 h₀ hg₀
  obtain ⟨a1, b1⟩ := Root.root_bracket (10 * L₀) hL1 h₁ hg₁
  obtain ⟨a2, b2⟩ := Root.root_bracket (L₀ / 10) hL2 h₂ hg₂
  obtain ⟨e0, f0⟩ := eta_L0
  obtain ⟨e1, f1⟩ := eta_10L0
  obtain ⟨e2, f2⟩ := eta_L0_10
  constructor
  · rw [abs_sub_lt_iff]
    constructor <;> linarith
  · rw [abs_sub_lt_iff]
    constructor <;> linarith

/-- `K/ln L₀ = 0.0113`, the correction to the slope of `g` -/
lemma slope_correction :
    (0.01132 : ℝ) < (3 / 2 * Real.log 2 + Real.log π / 2) / Real.log L₀ ∧
      (3 / 2 * Real.log 2 + Real.log π / 2) / Real.log L₀ < 0.01133 := by
  obtain ⟨h1, h2⟩ := log_L0_bounds
  obtain ⟨hp1, hp2⟩ := log_pi_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  have hL0 : 0 < Real.log L₀ := lt_trans (by norm_num) h1
  constructor
  · rw [lt_div_iff₀ hL0]
    nlinarith
  · rw [div_lt_iff₀ hL0]
    nlinarith

/-- **Pixels of side `2ℓ_P` move the root up by `0.010`** (Sec. VI): with the count divided by
four, the root `d₄` lies above the root `d₀` by between `0.0097` and `0.0099`. -/
theorem pixel_shift_val {d₀ d₄ : ℝ} (h₀ : d₀ ∈ Icc (2 : ℝ) 4) (h₄ : d₄ ∈ Icc (2 : ℝ) 4)
    (hg₀ : Root.g L₀ d₀ = 0) (hg₄ : Root.g L₀ d₄ = Real.log 4 / Real.log L₀) :
    (0.0097 : ℝ) < d₄ - d₀ ∧ d₄ - d₀ < 0.0099 := by
  obtain ⟨s1, s2⟩ := pixel_choice
  obtain ⟨q1, q2⟩ := slope_correction
  obtain ⟨h1, h2⟩ := Root.pixel_shift L₀ four_pi_lt_L0 h₀ h₄ hg₀ hg₄ (by linarith)
  constructor
  · linarith
  · rcases lt_or_ge (d₄ - d₀) 0.0099 with h | h
    · exact h
    · exfalso
      nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_pos.2 q2).le]

/-- **The factor that puts the root at `7/2` lies between `1.27 × 10³⁰` and `1.44 × 10³⁰`**
(Sec. VI): it is `√L₀ · C(7/2)` with `√L₀ = 8 × 10³⁰` and `1/2π ≤ C(7/2) ≤ 1/π^{3/2}`. -/
theorem seven_halves_factor_val :
    (1.27 : ℝ) * 10 ^ 30 < Real.exp (Real.log L₀ * Root.g L₀ (7 / 2)) ∧
      Real.exp (Real.log L₀ * Root.g L₀ (7 / 2)) < 1.44 * 10 ^ 30 := by
  obtain ⟨heq, hlo, hhi⟩ := Root.seven_halves_factor L₀ (by norm_num)
  have hsqrt : Real.sqrt L₀ = 8 * 10 ^ 30 := by
    rw [show (64 : ℝ) * 10 ^ 60 = (8 * 10 ^ 30) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [heq, Real.exp_add, Real.exp_log (Real.sqrt_pos.2 (by norm_num)), hsqrt]
  have hsπ0 : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
  have hsπ : (1.7724 : ℝ) < Real.sqrt π := by
    rw [Real.lt_sqrt (by positivity)]
    nlinarith [pi_lo]
  have e1 : Real.exp (-Real.log (2 * π)) = 1 / (2 * π) := by
    rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  have e2 : Real.exp (-(3 / 2) * Real.log π) = 1 / (π * Real.sqrt π) := by
    have e : -(3 / 2) * Real.log π = -(Real.log π + Real.log (Real.sqrt π)) := by
      rw [Real.log_sqrt pi_pos.le]
      ring
    rw [e, Real.exp_neg, Real.exp_add, Real.exp_log pi_pos, Real.exp_log hsπ0, one_div]
  have c1 : 1 / (2 * π) ≤ Real.exp (Root.logC (7 / 2)) := by
    rw [← e1]
    exact Real.exp_le_exp.2 hlo
  have c2 : Real.exp (Root.logC (7 / 2)) ≤ 1 / (π * Real.sqrt π) := by
    rw [← e2]
    exact Real.exp_le_exp.2 hhi
  constructor
  · calc (1.27 : ℝ) * 10 ^ 30 < 8 * 10 ^ 30 * (1 / (2 * π)) := by
          rw [mul_one_div, lt_div_iff₀ (by positivity)]
          nlinarith [pi_hi]
      _ ≤ 8 * 10 ^ 30 * Real.exp (Root.logC (7 / 2)) :=
          mul_le_mul_of_nonneg_left c1 (by norm_num)
  · calc 8 * 10 ^ 30 * Real.exp (Root.logC (7 / 2)) ≤ 8 * 10 ^ 30 * (1 / (π * Real.sqrt π)) :=
          mul_le_mul_of_nonneg_left c2 (by norm_num)
      _ < 1.44 * 10 ^ 30 := by
          rw [mul_one_div, div_lt_iff₀ (by positivity)]
          nlinarith [pi_lo, hsπ, mul_pos (sub_pos.2 pi_lo) (sub_pos.2 hsπ)]

/-- **The factor that puts the root at `5/2` lies between `1.13 × 10³¹` and `1.42 × 10³¹`**
(Sec. VI): the count must be multiplied by `√L₀/C(5/2)`, between `√(2L₀)` and `√(πL₀)`. -/
theorem five_halves_factor_val :
    (1.13 : ℝ) * 10 ^ 31 < Real.exp (-(Real.log L₀ * Root.g L₀ (5 / 2))) ∧
      Real.exp (-(Real.log L₀ * Root.g L₀ (5 / 2))) < 1.42 * 10 ^ 31 := by
  obtain ⟨heq, hlo, hhi⟩ := Root.five_halves_factor L₀ (by norm_num)
  have hsqrt : Real.sqrt L₀ = 8 * 10 ^ 30 := by
    rw [show (64 : ℝ) * 10 ^ 60 = (8 * 10 ^ 30) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [heq, Real.exp_sub, Real.exp_log (Real.sqrt_pos.2 (by norm_num)), hsqrt]
  have hs2 : (1.4142 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by positivity)]
    norm_num
  have hsπ : Real.sqrt π < 1.7725 := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith [pi_hi]
  have hsπ0 : 0 < Real.sqrt π := Real.sqrt_pos.2 pi_pos
  have hs20 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have e1 : Real.exp (-(Real.log π / 2)) = 1 / Real.sqrt π := by
    rw [← Real.log_sqrt pi_pos.le, Real.exp_neg, Real.exp_log hsπ0, one_div]
  have e2 : Real.exp (-(Real.log 2 / 2)) = 1 / Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.exp_neg, Real.exp_log hs20, one_div]
  have c1 : 1 / Real.sqrt π ≤ Real.exp (Root.logC (5 / 2)) := by
    rw [← e1]
    exact Real.exp_le_exp.2 hlo
  have c2 : Real.exp (Root.logC (5 / 2)) ≤ 1 / Real.sqrt 2 := by
    rw [← e2]
    exact Real.exp_le_exp.2 hhi
  have hexp : 0 < Real.exp (Root.logC (5 / 2)) := Real.exp_pos _
  constructor
  · rw [lt_div_iff₀ hexp]
    calc (1.13 : ℝ) * 10 ^ 31 * Real.exp (Root.logC (5 / 2))
        ≤ 1.13 * 10 ^ 31 * (1 / Real.sqrt 2) := mul_le_mul_of_nonneg_left c2 (by norm_num)
      _ < 8 * 10 ^ 30 := by
          rw [mul_one_div, div_lt_iff₀ hs20]
          nlinarith [hs2]
  · rw [div_lt_iff₀ hexp]
    calc (8 : ℝ) * 10 ^ 30 < 1.42 * 10 ^ 31 * (1 / Real.sqrt π) := by
          rw [mul_one_div, lt_div_iff₀ hsπ0]
          nlinarith [hsπ]
      _ ≤ 1.42 * 10 ^ 31 * Real.exp (Root.logC (5 / 2)) :=
          mul_le_mul_of_nonneg_left c1 (by norm_num)

end DimensionNumerics
end Register
