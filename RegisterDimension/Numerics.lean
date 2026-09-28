import RegisterDimension.Root
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# The numbers of *The Dimension of Space from the Granularity of Hilbert Space* (v16-34)

The paper does not fix the value of `L`.  The largest ring we observe is a great circle of the de
Sitter horizon, so with a cell near the Planck length `L` lies between `10⁶¹` and `10⁶²`, and every
number below is certified for every `L` in that range.  The bounds on `π`, `ln 2` and `e` are
Mathlib's; those on `ln π` and `ln 10` are derived here from `e^x < 1/(1 − x)` and `1 + x ≤ e^x`.

* `log_L_range`: `140.422 < ln L < 142.7984`.
* `leading_term_range`, `bound_value_range`, `pixel_choice_range`: `3 + ln π/ln L = 3.008`,
  `ln 4π/ln L = 0.018`, `ln 4/ln L = 0.010` (Sec. VI).
* `root_range`: the root of the relaxed count lies between `3.0080` and `3.0083`, so it is `3.008`,
  and it is the only solution below `L²/2π`, which exceeds `10¹²¹` (`uniqueness_range`).
* `pixel_shift_range`: pixels of four cells move the root up by between `0.0097` and `0.0100`.
* `seven_halves_range`, `five_halves_range`: the factor that puts the root at `7/2` lies between
  `5 × 10²⁹` and `2 × 10³⁰`; the one that puts it at `5/2` exceeds `4 × 10³⁰`.
* `capacity_range`: `⌊log₂ L⌋` lies between `202` and `205`.
* `inv_pi_val`, `pi_val`: a cell of the grid is `0.318` of a pixel, and the ratio of the counts at
  `d = 3` and `d = 2` is `3.14`.
-/

set_option exponentiation.threshold 50000

open Real Set

namespace Register
namespace DimensionNumerics

lemma pi_lo : (3.141592 : ℝ) < π := Real.pi_gt_d6
lemma pi_hi : π < (3.141593 : ℝ) := Real.pi_lt_d6

/-- **`1/π = 0.318`**: a cell of the grid on the horizon is `ℓ²/π`, `0.318` of a pixel (Sec. VII). -/
theorem inv_pi_val : (0.3183 : ℝ) < 1 / π ∧ 1 / π < 0.3184 := by
  constructor
  · rw [lt_div_iff₀ pi_pos]
    linarith [pi_hi]
  · rw [div_lt_iff₀ pi_pos]
    linarith [pi_lo]

/-- **The ratio of the counts at `d = 3` and `d = 2` is `π = 3.14`** (Table I). -/
theorem pi_val : (3.14 : ℝ) < π ∧ π < 3.142 := ⟨by linarith [pi_lo], by linarith [pi_hi]⟩

/-! ### Logarithms: `ln π`, `ln 10`, and `ln L` over the range -/

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

/-- **`ln L` over the range**: for `10⁶¹ ≤ L ≤ 10⁶²`, `140.422 < ln L < 142.7984`. -/
theorem log_L_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    (140.422 : ℝ) < Real.log L ∧ Real.log L < 142.7984 := by
  obtain ⟨ht1, ht2⟩ := log_ten_bounds
  have hpos : (0 : ℝ) < (10 : ℝ) ^ 61 := by positivity
  have a := Real.log_le_log hpos h1
  have b := Real.log_le_log (lt_of_lt_of_le hpos h1) h2
  rw [Real.log_pow] at a b
  push_cast at a b
  constructor <;> linarith

lemma four_pi_lt {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) : 4 * π < L := by
  have : 4 * π < (10 : ℝ) ^ 61 := by nlinarith [pi_hi]
  linarith

/-! ### The relaxed count over the range -/

/-- **`3 + ln π/ln L = 3.008`**, the leading term of the root (Sec. VI). -/
theorem leading_term_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    (3.0080 : ℝ) < 3 + Real.log π / Real.log L ∧ 3 + Real.log π / Real.log L < 3.0082 := by
  obtain ⟨x1, x2⟩ := log_L_range h1 h2
  obtain ⟨p1, p2⟩ := log_pi_bounds
  have hx : 0 < Real.log L := by linarith
  have a : (0.0080 : ℝ) < Real.log π / Real.log L := by
    rw [lt_div_iff₀ hx]
    linarith
  have b : Real.log π / Real.log L < 0.0082 := by
    rw [div_lt_iff₀ hx]
    linarith
  constructor <;> linarith

/-- **`ln 4π/ln L = 0.018`**, the bound of Eq. (bound) (Sec. VI). -/
theorem bound_value_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    (0.0177 : ℝ) < Real.log (4 * π) / Real.log L ∧ Real.log (4 * π) / Real.log L < 0.0181 := by
  obtain ⟨x1, x2⟩ := log_L_range h1 h2
  obtain ⟨p1, p2⟩ := log_pi_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  have hx : 0 < Real.log L := by linarith
  rw [Root.log_four_pi]
  constructor
  · rw [lt_div_iff₀ hx]
    linarith
  · rw [div_lt_iff₀ hx]
    linarith

/-- **`ln 4/ln L = 0.010`**: the shift of the root for pixels of four cells (Sec. VI). -/
theorem pixel_choice_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    (0.0097 : ℝ) < Real.log 4 / Real.log L ∧ Real.log 4 / Real.log L < 0.0099 := by
  obtain ⟨x1, x2⟩ := log_L_range h1 h2
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  have hx : 0 < Real.log L := by linarith
  rw [Root.log_four]
  constructor
  · rw [lt_div_iff₀ hx]
    linarith
  · rw [div_lt_iff₀ hx]
    linarith

/-- **The relaxed count has its only solution below `L²/2π` at `3.008`** (Sec. VI), for every `L`
between `10⁶¹` and `10⁶²`: the root lies between `3.0080` and `3.0083`. -/
theorem root_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    ∃ d ∈ Icc (2 : ℝ) 4, Root.g L d = 0 ∧ (3.0080 : ℝ) < d ∧ d < 3.0083 ∧
      ∀ d', 0 < d' → d' < L ^ 2 / (2 * π) → Root.g L d' = 0 → d' = d := by
  obtain ⟨d, hd, hg, -, ⟨hb1, hb2⟩, huniq⟩ := Root.unique_root L (four_pi_lt h1)
  obtain ⟨x1, x2⟩ := log_L_range h1 h2
  obtain ⟨p1, p2⟩ := log_pi_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  rw [Root.log_four] at hb2
  have e1 : (0.00801 : ℝ) ≤ Real.log π / (Real.log L - Real.log π) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have e2 : Real.log π / (Real.log L - 2 * Real.log 2) ≤ 0.00825 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  exact ⟨d, hd, hg, by linarith, by linarith, huniq⟩

/-- **`L²/2π` exceeds `10¹²¹`**: the range on which the root is the only solution. -/
theorem uniqueness_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) : (10 : ℝ) ^ 121 < L ^ 2 / (2 * π) := by
  have hsq : ((10 : ℝ) ^ 61) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [lt_div_iff₀ (by positivity)]
  have : (10 : ℝ) ^ 121 * (2 * π) < ((10 : ℝ) ^ 61) ^ 2 := by nlinarith [pi_hi]
  linarith

/-- `K/ln L`, the correction to the slope of `g`, is below `0.0115` -/
lemma slope_correction_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    (3 / 2 * Real.log 2 + Real.log π / 2) < Real.log L := by
  obtain ⟨x1, x2⟩ := log_L_range h1 h2
  obtain ⟨p1, p2⟩ := log_pi_bounds
  have hl2h := Real.log_two_lt_d9
  linarith

/-- **Pixels of four cells move the root up by `0.010`** (Sec. VI): with the count divided by four,
the root `d₄` lies above the root `d₀` by between `0.0097` and `0.0100`. -/
theorem pixel_shift_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62)
    {d₀ d₄ : ℝ} (h₀ : d₀ ∈ Icc (2 : ℝ) 4) (h₄ : d₄ ∈ Icc (2 : ℝ) 4)
    (hg₀ : Root.g L d₀ = 0) (hg₄ : Root.g L d₄ = Real.log 4 / Real.log L) :
    (0.0097 : ℝ) < d₄ - d₀ ∧ d₄ - d₀ < 0.0100 := by
  obtain ⟨s1, s2⟩ := pixel_choice_range h1 h2
  obtain ⟨x1, x2⟩ := log_L_range h1 h2
  obtain ⟨p1, p2⟩ := log_pi_bounds
  have hl2l := Real.log_two_gt_d9
  have hl2h := Real.log_two_lt_d9
  have hx : 0 < Real.log L := by linarith
  have hs0 : 0 ≤ Real.log 4 / Real.log L := by linarith
  obtain ⟨hlo, hhi⟩ := Root.pixel_shift L (four_pi_lt h1) h₀ h₄ hg₀ hg₄ hs0
  constructor
  · linarith
  · set K := 3 / 2 * Real.log 2 + Real.log π / 2 with hK
    have hmul := mul_le_mul_of_nonneg_right hhi hx.le
    have ea : (1 - K / Real.log L) * Real.log L = Real.log L - K := by
      rw [sub_mul, one_mul, div_mul_cancel₀ K hx.ne']
    have eb : Real.log 4 / Real.log L * Real.log L = Real.log 4 := div_mul_cancel₀ _ hx.ne'
    rw [mul_assoc, ea, eb] at hmul
    have hK0 : 0 ≤ Real.log L - K := by
      have := slope_correction_range h1 h2
      linarith
    rw [Root.log_four] at hmul
    rcases lt_or_ge (d₄ - d₀) 0.0100 with h | h
    · exact h
    · exfalso
      have h3 := mul_le_mul_of_nonneg_right h hK0
      linarith

lemma sqrt_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    (3.16 : ℝ) * 10 ^ 30 ≤ Real.sqrt L ∧ Real.sqrt L ≤ 10 ^ 31 := by
  constructor
  · calc (3.16 : ℝ) * 10 ^ 30 = Real.sqrt (((3.16 : ℝ) * 10 ^ 30) ^ 2) :=
          (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt (by nlinarith)
  · calc Real.sqrt L ≤ Real.sqrt (((10 : ℝ) ^ 31) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 10 ^ 31 := Real.sqrt_sq (by norm_num)

/-- **The factor that puts the root at `7/2` lies between `5 × 10²⁹` and `2 × 10³⁰`** (Sec. VI):
it is `√L · C(7/2)`, and `1/2π ≤ C(7/2) ≤ 1/π^{3/2}`. -/
theorem seven_halves_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    (5 : ℝ) * 10 ^ 29 < Real.exp (Real.log L * Root.g L (7 / 2)) ∧
      Real.exp (Real.log L * Root.g L (7 / 2)) < 2 * 10 ^ 30 := by
  have hL1 : 1 < L := by
    have : (1 : ℝ) < 10 ^ 61 := by norm_num
    linarith
  obtain ⟨heq, hlo, hhi⟩ := Root.seven_halves_factor L hL1
  obtain ⟨q1, q2⟩ := sqrt_range h1 h2
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  rw [heq, Real.exp_add, Real.exp_log hsL]
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
  have hE : 0 < Real.exp (Root.logC (7 / 2)) := Real.exp_pos _
  constructor
  · calc (5 : ℝ) * 10 ^ 29 < 3.16 * 10 ^ 30 * (1 / (2 * π)) := by
          rw [mul_one_div, lt_div_iff₀ (by positivity)]
          nlinarith [pi_hi]
      _ ≤ Real.sqrt L * Real.exp (Root.logC (7 / 2)) :=
          mul_le_mul q1 c1 (by positivity) hsL.le
  · calc Real.sqrt L * Real.exp (Root.logC (7 / 2)) ≤ 10 ^ 31 * (1 / (π * Real.sqrt π)) :=
          mul_le_mul q2 c2 hE.le (by positivity)
      _ < 2 * 10 ^ 30 := by
          rw [mul_one_div, div_lt_iff₀ (by positivity)]
          nlinarith [pi_lo, hsπ, mul_pos (sub_pos.2 pi_lo) (sub_pos.2 hsπ)]

/-- **The factor that puts the root at `5/2` exceeds `4 × 10³⁰`** (Sec. VI): the count must be
multiplied by `√L/C(5/2)`, and `C(5/2) ≤ 1/√2`. -/
theorem five_halves_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    (4 : ℝ) * 10 ^ 30 < Real.exp (-(Real.log L * Root.g L (5 / 2))) := by
  have hL1 : 1 < L := by
    have : (1 : ℝ) < 10 ^ 61 := by norm_num
    linarith
  obtain ⟨heq, -, hhi⟩ := Root.five_halves_factor L hL1
  obtain ⟨q1, -⟩ := sqrt_range h1 h2
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  rw [heq, Real.exp_sub, Real.exp_log hsL]
  have hs20 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (1.4142 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by positivity)]
    norm_num
  have e2 : Real.exp (-(Real.log 2 / 2)) = 1 / Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.exp_neg, Real.exp_log hs20, one_div]
  have c2 : Real.exp (Root.logC (5 / 2)) ≤ 1 / Real.sqrt 2 := by
    rw [← e2]
    exact Real.exp_le_exp.2 hhi
  have hE : 0 < Real.exp (Root.logC (5 / 2)) := Real.exp_pos _
  rw [lt_div_iff₀ hE]
  calc (4 : ℝ) * 10 ^ 30 * Real.exp (Root.logC (5 / 2)) ≤ 4 * 10 ^ 30 * (1 / Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left c2 (by norm_num)
    _ < 3.16 * 10 ^ 30 := by
        rw [mul_one_div, div_lt_iff₀ hs20]
        nlinarith [hs2]
    _ ≤ Real.sqrt L := q1

/-! ### Capacity -/

/-- **`⌊log₂ L⌋` lies between `202` and `205`**: `2²⁰²` fits in `L`, and `2^N ≤ L` only for `N ≤ 205`. -/
theorem capacity_range {L : ℝ} (h1 : (10 : ℝ) ^ 61 ≤ L) (h2 : L ≤ (10 : ℝ) ^ 62) :
    (2 : ℝ) ^ 202 ≤ L ∧ ∀ N : ℕ, (2 : ℝ) ^ N ≤ L → N ≤ 205 := by
  constructor
  · have : (2 : ℝ) ^ 202 ≤ 10 ^ 61 := by norm_num
    linarith
  · intro N hN
    by_contra hlt
    have h206 : 206 ≤ N := by omega
    have a : (2 : ℝ) ^ 206 ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) h206
    have b : (10 : ℝ) ^ 62 < 2 ^ 206 := by norm_num
    linarith

end DimensionNumerics
end Register
