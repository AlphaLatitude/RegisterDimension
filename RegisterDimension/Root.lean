import RegisterDimension.Sphere
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The relaxed count: Sec. VI of *The Dimension of Space from the Granularity of Hilbert Space* (v16-29)

Sec. VI asks what dimension the horizon would have if the sphere of radius `Lℓ_P/2π` held exactly
`L²` Planck pixels, with `d` allowed to be real: the equation `Ω_{d−1}(L/2π)^{d−1} = L²`, that is
`g(d) = 0` with `g(d) = (d − 3) + ln C(d)/ln L` and `C(d) = Ω_{d−1}/(2π)^{d−1}`, Eqs. (g)–(C).
Everything here rests on one fact about `Γ`: `ln Γ` is convex on `(0, ∞)` (the Bohr–Mollerup
theorem, Mathlib's `Real.convexOn_log_Gamma`), together with `Γ(1) = Γ(2) = 1`,
`Γ(1/2) = √π`, and `Γ(x + 1) = xΓ(x)`.  No derivative is taken: where the paper argues with the
digamma function, the files argue with the slopes of `ln Γ`.

* `f_nonpos`, `f_ge`: on `[1, 2]`, `−(x − 1) ln π ≤ ln Γ(x) ≤ 0`.
* `logC_eq`: `ln C(d) = (2 − d) ln 2 + (1 − d/2) ln π − ln Γ(d/2)`.
* `logC_nonpos`, `logC_ge`, `logC_strictAnti`: on `[2, 4]`, `C` decreases and
  `1/4π ≤ C(d) ≤ 1`.
* `g_two`, `g_four_eq`, `g_four`: `g(2) = −1` and `g(4) = 1 − ln 4π/ln L > 0` for `L > 4π`.
* `root_exists`: `g` has a root in `[2, 4]` (the intermediate value theorem).
* `g_strictMono`: `g` is strictly increasing on `(0, L²/2π)`, for every `L > 1`.
* `root_bound`: any root in `[2, 4]` satisfies `0 ≤ d − 3 ≤ ln 4π/ln L`, Eq. (bound).
* `f_near_three_halves`, `logC_near_three`, `root_bracket`: the chords of `ln Γ` at `3/2` give
  `ln π/(ln L − ln π) ≤ d − 3 ≤ ln π/(ln L − ln 4)` at any root in `[2, 4]`, which fixes the
  root to four decimals at the paper's `L` (`Numerics.lean`).
* `unique_root`: the root exists, is unique in `(0, L²/2π)`, and obeys both brackets.
* `g_slope`, `pixel_shift`: dividing the count by `c ≥ 1` moves the root up by at least
  `ln c/ln L` and at most `ln c/ln L` over `1 − K/ln L`, `K = (3/2) ln 2 + ½ ln π`.
* `seven_halves_factor`, `five_halves_factor`: the factor that puts the root at `7/2` is
  `√L · C(7/2)`, between `√L/2π` and `√L/π^{3/2}`; the one that puts it at `5/2` is `√L/C(5/2)`,
  between `√(2L)` and `√(πL)`.
-/

open Real Set

namespace Register
namespace Root

/-- `f = ln ∘ Γ`, convex on `(0, ∞)` by the Bohr–Mollerup theorem -/
noncomputable def f (x : ℝ) : ℝ := Real.log (Real.Gamma x)

lemma f_convex : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma

lemma f_one : f 1 = 0 := by
  simp [f, Real.Gamma_one]

lemma f_two : f 2 = 0 := by
  simp [f]

lemma f_half : f (1 / 2) = Real.log π / 2 := by
  rw [f, Real.Gamma_one_half_eq, Real.log_sqrt pi_pos.le]

lemma f_three_halves : f (3 / 2) = Real.log π / 2 - Real.log 2 := by
  rw [f, Sphere.Gamma_three_halves, Real.log_div (Real.sqrt_pos.2 pi_pos).ne' two_ne_zero,
    Real.log_sqrt pi_pos.le]

lemma log_pi_pos : 0 < Real.log π :=
  Real.log_pos (by linarith [Real.pi_gt_three])

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two

lemma log_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

lemma log_four_pi : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) pi_pos.ne', log_four]

lemma log_four_pi_pos : 0 < Real.log (4 * π) :=
  Real.log_pos (by nlinarith [Real.pi_gt_three])

lemma log_L_pos {L : ℝ} (hL : 4 * π < L) : 0 < Real.log L :=
  log_four_pi_pos.trans (Real.log_lt_log (by positivity) hL)

lemma one_lt_of_four_pi_lt {L : ℝ} (hL : 4 * π < L) : 1 < L := by
  linarith [Real.pi_gt_three]

/-- convexity: for `0 < x < y < z` the slope of `f` over `[x, y]` is at most that over `[y, z]` -/
lemma slope_le {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
  f_convex.slope_mono_adjacent (mem_Ioi.2 hx) (mem_Ioi.2 (by linarith)) hxy hyz

/-- **`Γ ≤ 1` on `[1, 2]`**: `ln Γ` lies under its chord between `1` and `2`, where it vanishes. -/
theorem f_nonpos {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : f x ≤ 0 := by
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · rw [f_one]
  rcases eq_or_lt_of_le h2 with rfl | h2'
  · rw [f_two]
  have h := slope_le (by norm_num : (0 : ℝ) < 1) h1' h2'
  rw [f_one, f_two] at h
  have hx1 : 0 < x - 1 := by linarith
  have hx2 : 0 < 2 - x := by linarith
  rw [div_le_iff₀ hx1, div_mul_eq_mul_div, le_div_iff₀ hx2] at h
  nlinarith

/-- **`Γ(x) ≥ π^{−(x−1)}` on `[1, ∞)`**: the slope of `ln Γ` from `1` to `x` is at least its slope
from `1/2` to `1`, which is `−ln π`. -/
theorem f_ge {x : ℝ} (h1 : 1 ≤ x) : -(x - 1) * Real.log π ≤ f x := by
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · rw [f_one]
    norm_num
  have h := slope_le (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) h1'
  rw [f_one, f_half] at h
  have hx1 : 0 < x - 1 := by linarith
  rw [le_div_iff₀ hx1] at h
  norm_num at h
  nlinarith [h]

lemma f_add_one {b : ℝ} (hb : 0 < b) : f (b + 1) = Real.log b + f b := by
  rw [f, f, Real.Gamma_add_one hb.ne', Real.log_mul hb.ne' (Real.Gamma_pos_of_pos hb).ne']

/-- **The slope of `ln Γ` over `[a, b]` is at most `ln b`**: by convexity it is at most the slope
over `[b, b + 1]`, which is `ln b` since `Γ(b + 1) = bΓ(b)`. -/
theorem slope_le_log {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (f b - f a) / (b - a) ≤ Real.log b := by
  have h := slope_le ha hab (by linarith : b < b + 1)
  rw [f_add_one (by linarith)] at h
  simpa using h

/-- `ln C(d)` in closed form, with `C(d) = Ω_{d−1}/(2π)^{d−1}` the pixel-to-cell ratio of Eq. (C) -/
noncomputable def logC (d : ℝ) : ℝ :=
  (2 - d) * Real.log 2 + (1 - d / 2) * Real.log π - f (d / 2)

/-- **`logC` is the logarithm of `C`**, Eq. (C). -/
theorem logC_eq (d : ℝ) (hd : 0 < d) : logC d = Real.log (Sphere.C d) := by
  unfold logC Sphere.C Sphere.Ω f
  have hg : 0 < Real.Gamma (d / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hp : 0 < π ^ (d / 2) := by positivity
  have hΩ : 0 < 2 * π ^ (d / 2) / Real.Gamma (d / 2) := div_pos (by positivity) hg
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hq : 0 < (2 * π) ^ (d - 1) := by positivity
  rw [Real.log_div hΩ.ne' hq.ne', Real.log_div (mul_pos two_pos hp).ne' hg.ne',
    Real.log_mul two_ne_zero hp.ne', Real.log_rpow pi_pos, Real.log_rpow h2π,
    Real.log_mul two_ne_zero pi_pos.ne']
  ring

/-- **`C(d) ≤ 1` for `d ≥ 2`**, Eq. (C): from `Γ(x) ≥ π^{−(x−1)}`. -/
theorem logC_nonpos {d : ℝ} (h2 : 2 ≤ d) : logC d ≤ 0 := by
  unfold logC
  have hf := f_ge (x := d / 2) (by linarith)
  nlinarith [hf, log_two_pos]

/-- **`C(d) ≥ 1/4π` on `[2, 4]`**, Eq. (C): from `Γ ≤ 1`. -/
theorem logC_ge {d : ℝ} (h2 : 2 ≤ d) (h4 : d ≤ 4) : -Real.log (4 * π) ≤ logC d := by
  unfold logC
  have hf := f_nonpos (x := d / 2) (by linarith) (by linarith)
  rw [log_four_pi]
  nlinarith [hf, log_two_pos, log_pi_pos]

/-- **`C` decreases for `d ≥ 2`** (Sec. VI): the slope of `ln Γ` over `[x/2, y/2]` is at least the
slope over `[1/2, x/2]`, which is at least `−ln π`, so `ln C` falls by at least `(y − x) ln 2`. -/
theorem logC_strictAnti {x y : ℝ} (hx : 2 ≤ x) (hxy : x < y) : logC y < logC x := by
  have hslope := slope_le (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (1 / 2 : ℝ) < x / 2)
    (by linarith : x / 2 < y / 2)
  have hfx := f_ge (x := x / 2) (by linarith)
  rw [f_half] at hslope
  have hpos1 : 0 < x / 2 - 1 / 2 := by linarith
  have hpos2 : 0 < y / 2 - x / 2 := by linarith
  have hlow : -Real.log π ≤ (f (x / 2) - Real.log π / 2) / (x / 2 - 1 / 2) := by
    rw [le_div_iff₀ hpos1]
    nlinarith [hfx]
  have h2 := hlow.trans hslope
  rw [le_div_iff₀ hpos2] at h2
  unfold logC
  nlinarith [h2, log_two_pos, hxy]

/-- the fall of `ln C` from `x` to `y`: at most `(y − x)(ln 2 + ½ ln π + ½ ln(y/2))` -/
lemma logC_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    logC x - logC y ≤ (y - x) * (Real.log 2 + Real.log π / 2 + Real.log (y / 2) / 2) := by
  have hslope := slope_le_log (a := x / 2) (b := y / 2) (by linarith) (by linarith)
  have hpos : 0 < y / 2 - x / 2 := by linarith
  rw [div_le_iff₀ hpos] at hslope
  unfold logC
  nlinarith [hslope]

/-- `g(d) = (d − 3) + ln C(d)/ln L`, Eq. (g): the relaxed count is `g(d) = 0` -/
noncomputable def g (L d : ℝ) : ℝ := (d - 3) + logC d / Real.log L

/-- **`g(2) = −1`**: in two dimensions the count is short by a factor `L`. -/
theorem g_two (L : ℝ) : g L 2 = -1 := by
  unfold g logC
  rw [show (2 : ℝ) / 2 = 1 by norm_num, f_one]
  ring

/-- **`g(4) = 1 − ln 4π/ln L`**: in four dimensions the count exceeds `L²` by `L/4π`. -/
theorem g_four_eq (L : ℝ) : g L 4 = 1 - Real.log (4 * π) / Real.log L := by
  unfold g logC
  rw [show (4 : ℝ) / 2 = 2 by norm_num, f_two, log_four_pi]
  ring

/-- **`g(4) > 0` whenever `L > 4π`.** -/
theorem g_four (L : ℝ) (hL : 4 * π < L) : 0 < g L 4 := by
  rw [g_four_eq, sub_pos, div_lt_one (log_L_pos hL)]
  exact Real.log_lt_log (by positivity) hL

/-- `logC` is continuous on `[2, 4]`: `Γ` is continuous and positive on `[1, 2]`. -/
theorem logC_continuousOn : ContinuousOn logC (Icc 2 4) := by
  have hf : ContinuousOn (fun d : ℝ => f (d / 2)) (Icc 2 4) := by
    intro d hd
    have hpos : 0 < d / 2 := by linarith [hd.1]
    have hG : ContinuousAt Real.Gamma (d / 2) :=
      (Real.differentiableAt_Gamma (fun m => by
        intro hm
        have := Nat.cast_nonneg (α := ℝ) m
        linarith)).continuousAt
    have hlog : ContinuousAt Real.log (Real.Gamma (d / 2)) :=
      Real.continuousAt_log (Real.Gamma_pos_of_pos hpos).ne'
    have hhalf : ContinuousAt (fun d : ℝ => d / 2) d := continuousAt_id.div_const 2
    exact (hlog.comp (f := Real.Gamma ∘ fun d : ℝ => d / 2)
      (hG.comp (f := fun d : ℝ => d / 2) hhalf)).continuousWithinAt
  have hpoly : Continuous (fun d : ℝ => (2 - d) * Real.log 2 + (1 - d / 2) * Real.log π) := by
    fun_prop
  unfold logC
  exact hpoly.continuousOn.sub hf

/-- **The relaxed count reaches every value between `g(2)` and `g(4)`** on `[2, 4]`: `g` is
continuous (the intermediate value theorem). -/
theorem root_exists_general (L : ℝ) {s : ℝ} (hs2 : g L 2 ≤ s) (hs4 : s ≤ g L 4) :
    ∃ d ∈ Icc (2 : ℝ) 4, g L d = s := by
  have hcont : ContinuousOn (g L) (Icc 2 4) := by
    have h1 : ContinuousOn (fun d : ℝ => d - 3) (Icc 2 4) :=
      (continuous_id.sub continuous_const).continuousOn
    have h2 : ContinuousOn (fun d : ℝ => logC d / Real.log L) (Icc 2 4) :=
      logC_continuousOn.div_const _
    unfold g
    exact h1.add h2
  obtain ⟨d, hd, hgd⟩ := intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 4) hcont ⟨hs2, hs4⟩
  exact ⟨d, hd, hgd⟩

/-- **The relaxed count has a root in `[2, 4]`** (Sec. VI): `g(2) < 0 < g(4)`. -/
theorem root_exists (L : ℝ) (hL : 4 * π < L) : ∃ d ∈ Icc (2 : ℝ) 4, g L d = 0 :=
  root_exists_general L (by rw [g_two]; norm_num) (g_four L hL).le

/-- **`g` is strictly increasing on `(0, L²/2π)`** (Sec. VI), for every `L > 1`: `ln C` falls by
at most `(y − x)(ln 2 + ½ ln π + ½ ln(y/2))`, which is below `(y − x) ln L` as long as
`y < L²/2π`, so `d − 3` wins.  This is the sentence "the left side increases with `d` until the
growth of `Γ(d/2)` overtakes it, near `d ~ 10¹²³`": the turn lies at or beyond `L²/2π`. -/
theorem g_strictMono (L : ℝ) (hL : 1 < L) {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : y < L ^ 2 / (2 * π)) : g L x < g L y := by
  have hL0 : 0 < Real.log L := Real.log_pos hL
  have hL' : 0 < L := by linarith
  have h1 : y / 2 < L ^ 2 / (4 * π) := by
    have e : L ^ 2 / (4 * π) = L ^ 2 / (2 * π) / 2 := by ring
    rw [e]
    linarith
  have h2 : Real.log (y / 2) < Real.log (L ^ 2 / (4 * π)) := Real.log_lt_log (by linarith) h1
  have h3 : Real.log (L ^ 2 / (4 * π)) = 2 * Real.log L - 2 * Real.log 2 - Real.log π := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, log_four_pi]
    push_cast
    ring
  have hK := logC_sub_le hx hxy
  have key : (logC x - logC y) / Real.log L < y - x := by
    rw [div_lt_iff₀ hL0]
    calc logC x - logC y
        ≤ (y - x) * (Real.log 2 + Real.log π / 2 + Real.log (y / 2) / 2) := hK
      _ < (y - x) * Real.log L := by
          apply mul_lt_mul_of_pos_left ?_ (by linarith)
          linarith
  have hsd : logC x / Real.log L - logC y / Real.log L = (logC x - logC y) / Real.log L :=
    (sub_div _ _ _).symm
  unfold g
  linarith [key, hsd]

lemma four_lt_range {L : ℝ} (hL : 4 * π < L) : 4 < L ^ 2 / (2 * π) := by
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Real.pi_gt_three, mul_pos (by linarith : (0 : ℝ) < L - 4 * π)
    (by linarith [Real.pi_gt_three] : (0 : ℝ) < L + 4 * π)]

/-- **Any root in `[2, 4]` lies within `ln 4π/ln L` above three**, Eq. (bound): at a root
`d − 3 = −ln C(d)/ln L` and `−ln 4π ≤ ln C(d) ≤ 0`. -/
theorem root_bound (L : ℝ) (hL : 4 * π < L) {d : ℝ} (hd : d ∈ Icc (2 : ℝ) 4) (hg : g L d = 0) :
    0 ≤ d - 3 ∧ d - 3 ≤ Real.log (4 * π) / Real.log L := by
  have hL0 : 0 < Real.log L := log_L_pos hL
  have hC1 := logC_nonpos hd.1
  have hC2 := logC_ge hd.1 hd.2
  unfold g at hg
  have e : d - 3 = -logC d / Real.log L := by
    rw [neg_div]
    linarith
  rw [e]
  constructor
  · apply div_nonneg ?_ hL0.le
    linarith
  · rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_pos.2 hL0).le

/-- **`ln Γ` near `3/2`, by convexity**: for `0 < ε < 1/2`,
`(1 + 2ε) f(3/2) ≤ f(3/2 + ε) ≤ (1 − 2ε) f(3/2)`, where `f(3/2) = ½ ln π − ln 2`: the graph of
`ln Γ` between `3/2` and `2` lies above the line through `(1, 0)` and `(3/2, f(3/2))` and below
the chord from `(3/2, f(3/2))` to `(2, 0)`. -/
theorem f_near_three_halves {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    (1 + 2 * ε) * f (3 / 2) ≤ f (3 / 2 + ε) ∧ f (3 / 2 + ε) ≤ (1 - 2 * ε) * f (3 / 2) := by
  constructor
  · have h := slope_le (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2)
      (by linarith : (3 / 2 : ℝ) < 3 / 2 + ε)
    rw [f_one] at h
    have hε : 0 < 3 / 2 + ε - 3 / 2 := by linarith
    rw [le_div_iff₀ hε] at h
    norm_num at h
    nlinarith [h]
  · have h := slope_le (by norm_num : (0 : ℝ) < 3 / 2) (by linarith : (3 / 2 : ℝ) < 3 / 2 + ε)
      (by linarith : (3 / 2 : ℝ) + ε < 2)
    rw [f_two] at h
    have hε : 0 < 3 / 2 + ε - 3 / 2 := by linarith
    have hε' : 0 < 2 - (3 / 2 + ε) := by linarith
    rw [div_le_iff₀ hε, div_mul_eq_mul_div, le_div_iff₀ hε'] at h
    nlinarith [h]

/-- **`ln C` within one of three**: for `0 < η < 1`,
`−ln π − 2η ln 2 ≤ ln C(3 + η) ≤ −(1 + η) ln π`. -/
theorem logC_near_three {η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    -Real.log π - 2 * η * Real.log 2 ≤ logC (3 + η) ∧ logC (3 + η) ≤ -(1 + η) * Real.log π := by
  have hf := f_near_three_halves (ε := η / 2) (by linarith) (by linarith)
  rw [f_three_halves] at hf
  have e : (3 + η) / 2 = 3 / 2 + η / 2 := by ring
  unfold logC
  rw [e]
  constructor <;> nlinarith [hf.1, hf.2]

/-- **The bracket of Sec. VI, evaluated**: `g ≤ 0` at `3 + ln π/(ln L − ln π)` and `g ≥ 0` at
`3 + ln π/(ln L − ln 4)`, for `L > 4π`. -/
theorem g_at_bracket (L : ℝ) (hL : 4 * π < L) :
    g L (3 + Real.log π / (Real.log L - Real.log π)) ≤ 0 ∧
    0 ≤ g L (3 + Real.log π / (Real.log L - Real.log 4)) := by
  have hL0 : 0 < Real.log L := log_L_pos hL
  have hlogL : Real.log (4 * π) < Real.log L := Real.log_lt_log (by positivity) hL
  have hπ4 : Real.log π < Real.log 4 := Real.log_lt_log pi_pos (by linarith [Real.pi_lt_d6])
  rw [log_four_pi] at hlogL
  rw [log_four] at hπ4 ⊢
  have hd1 : 0 < Real.log L - Real.log π := by linarith [log_two_pos]
  have hd2 : 0 < Real.log L - 2 * Real.log 2 := by linarith [log_pi_pos]
  constructor
  · set η₁ := Real.log π / (Real.log L - Real.log π) with hη₁
    have hη₁0 : 0 < η₁ := div_pos log_pi_pos hd1
    have hη₁1 : η₁ < 1 := by
      rw [hη₁, div_lt_one hd1]
      linarith
    have hmul : η₁ * (Real.log L - Real.log π) = Real.log π := by
      rw [hη₁]
      exact div_mul_cancel₀ _ hd1.ne'
    have hC := (logC_near_three hη₁0 hη₁1).2
    have key : logC (3 + η₁) ≤ -η₁ * Real.log L := by nlinarith [hC, hmul]
    have key' : logC (3 + η₁) / Real.log L ≤ -η₁ := by
      rw [div_le_iff₀ hL0]
      exact key
    unfold g
    linarith
  · set η₂ := Real.log π / (Real.log L - 2 * Real.log 2) with hη₂
    have hη₂0 : 0 < η₂ := div_pos log_pi_pos hd2
    have hη₂1 : η₂ < 1 := by
      rw [hη₂, div_lt_one hd2]
      linarith
    have hmul : η₂ * (Real.log L - 2 * Real.log 2) = Real.log π := by
      rw [hη₂]
      exact div_mul_cancel₀ _ hd2.ne'
    have hC := (logC_near_three hη₂0 hη₂1).1
    have key : -η₂ * Real.log L ≤ logC (3 + η₂) := by nlinarith [hC, hmul]
    have key' : -η₂ ≤ logC (3 + η₂) / Real.log L := by
      rw [le_div_iff₀ hL0]
      exact key
    unfold g
    linarith

/-- **The bracket**: any root in `[2, 4]` satisfies
`ln π/(ln L − ln π) ≤ d − 3 ≤ ln π/(ln L − ln 4)`, for `L > 4π`.  Both ends are positive and
below one, `g` is strictly increasing on `(0, L²/2π)`, `g ≤ 0` at the lower end and `g ≥ 0` at the
upper one. -/
theorem root_bracket (L : ℝ) (hL : 4 * π < L) {d : ℝ} (hd : d ∈ Icc (2 : ℝ) 4)
    (hg : g L d = 0) :
    Real.log π / (Real.log L - Real.log π) ≤ d - 3 ∧
      d - 3 ≤ Real.log π / (Real.log L - Real.log 4) := by
  obtain ⟨hlo, hhi⟩ := g_at_bracket L hL
  have hL1 : 1 < L := one_lt_of_four_pi_lt hL
  have hrange := four_lt_range hL
  have hπ4 : Real.log π < Real.log 4 := Real.log_lt_log pi_pos (by linarith [Real.pi_lt_d6])
  have hlogL : Real.log (4 * π) < Real.log L := Real.log_lt_log (by positivity) hL
  rw [log_four_pi] at hlogL
  rw [log_four] at hπ4 ⊢
  have hd1 : 0 < Real.log L - Real.log π := by linarith [log_two_pos]
  have hd2 : 0 < Real.log L - 2 * Real.log 2 := by linarith [log_pi_pos]
  have hη₁1 : Real.log π / (Real.log L - Real.log π) < 1 := by
    rw [div_lt_one hd1]
    linarith
  have hη₂1 : Real.log π / (Real.log L - 2 * Real.log 2) < 1 := by
    rw [div_lt_one hd2]
    linarith
  have hη₁0 : 0 < Real.log π / (Real.log L - Real.log π) := div_pos log_pi_pos hd1
  have hη₂0 : 0 < Real.log π / (Real.log L - 2 * Real.log 2) := div_pos log_pi_pos hd2
  rw [log_four] at hhi
  constructor
  · rcases lt_or_ge (d - 3) (Real.log π / (Real.log L - Real.log π)) with hlt | hle
    · have := g_strictMono L hL1 (by linarith [hd.1]) (by linarith : d < 3 + Real.log π / (Real.log L - Real.log π))
        (by linarith)
      linarith
    · exact hle
  · rcases lt_or_ge (Real.log π / (Real.log L - 2 * Real.log 2)) (d - 3) with hlt | hle
    · have := g_strictMono L hL1 (by linarith) (by linarith : 3 + Real.log π / (Real.log L - 2 * Real.log 2) < d)
        (by linarith [hd.2])
      linarith
    · exact hle

/-- **The relaxed count has exactly one solution below `L²/2π`, and it lies within the
brackets** (Sec. VI, Eqs. (g), (root), (bound)), for every `L > 4π`: the root exists in `[2, 4]`,
it satisfies `0 ≤ d − 3 ≤ ln 4π/ln L` and `ln π/(ln L − ln π) ≤ d − 3 ≤ ln π/(ln L − ln 4)`, and no
other `d` in `(0, L²/2π)` solves the equation. -/
theorem unique_root (L : ℝ) (hL : 4 * π < L) :
    ∃ d ∈ Icc (2 : ℝ) 4, g L d = 0 ∧
      (0 ≤ d - 3 ∧ d - 3 ≤ Real.log (4 * π) / Real.log L) ∧
      (Real.log π / (Real.log L - Real.log π) ≤ d - 3 ∧
        d - 3 ≤ Real.log π / (Real.log L - Real.log 4)) ∧
      ∀ d', 0 < d' → d' < L ^ 2 / (2 * π) → g L d' = 0 → d' = d := by
  obtain ⟨d, hd, hgd⟩ := root_exists L hL
  have hL1 : 1 < L := one_lt_of_four_pi_lt hL
  have hrange := four_lt_range hL
  refine ⟨d, hd, hgd, root_bound L hL hd hgd, root_bracket L hL hd hgd, ?_⟩
  intro d' hd'0 hd'r hgd'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := g_strictMono L hL1 hd'0 hlt (by linarith [hd.2])
    linarith
  · have := g_strictMono L hL1 (by linarith [hd.1]) hgt hd'r
    linarith

/-- **The slope of `g` on `[2, 4]`**: for `2 ≤ x < y ≤ 4`,
`(y − x)(1 − K/ln L) ≤ g(y) − g(x) ≤ y − x` with `K = (3/2) ln 2 + ½ ln π`, since `ln C` falls,
and falls by at most `(y − x)K` (`ln(y/2) ≤ ln 2`). -/
theorem g_slope (L : ℝ) (hL : 1 < L) {x y : ℝ} (hx : 2 ≤ x) (hxy : x < y) (hy : y ≤ 4) :
    (y - x) * (1 - (3 / 2 * Real.log 2 + Real.log π / 2) / Real.log L) ≤ g L y - g L x ∧
      g L y - g L x ≤ y - x := by
  have hL0 : 0 < Real.log L := Real.log_pos hL
  have hinv : 0 < (Real.log L)⁻¹ := inv_pos.2 hL0
  have hK := logC_sub_le (by linarith) hxy
  have hlog : Real.log (y / 2) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
  have hanti := logC_strictAnti hx hxy
  have h1 : logC x - logC y ≤ (y - x) * (3 / 2 * Real.log 2 + Real.log π / 2) := by
    nlinarith [hK, hlog, hxy]
  have h2 := mul_le_mul_of_nonneg_right h1 hinv.le
  have h3 := mul_le_mul_of_nonneg_right hanti.le hinv.le
  unfold g
  simp only [div_eq_mul_inv]
  constructor <;> nlinarith [h2, h3]

/-- **Another pixel moves the root by about `ln c/ln L`** (Sec. VI).  Dividing the count by `c ≥ 1`
turns the equation into `g(d) = s` with `s = ln c/ln L ≥ 0`; if `d₀` solves `g = 0` and `d₁`
solves `g = s`, both in `[2, 4]`, then `s ≤ d₁ − d₀ ≤ s/(1 − K/ln L)`. -/
theorem pixel_shift (L : ℝ) (hL : 4 * π < L) {d₀ d₁ s : ℝ} (h₀ : d₀ ∈ Icc (2 : ℝ) 4)
    (h₁ : d₁ ∈ Icc (2 : ℝ) 4) (hg₀ : g L d₀ = 0) (hg₁ : g L d₁ = s) (hs : 0 ≤ s) :
    s ≤ d₁ - d₀ ∧ (d₁ - d₀) * (1 - (3 / 2 * Real.log 2 + Real.log π / 2) / Real.log L) ≤ s := by
  have hL1 : 1 < L := one_lt_of_four_pi_lt hL
  have hrange := four_lt_range hL
  rcases lt_trichotomy d₀ d₁ with hlt | heq | hgt
  · obtain ⟨hlo, hhi⟩ := g_slope L hL1 h₀.1 hlt h₁.2
    rw [hg₀, hg₁, sub_zero] at hlo hhi
    exact ⟨hhi, hlo⟩
  · subst heq
    rw [hg₀] at hg₁
    subst hg₁
    simp
  · have := g_strictMono L hL1 (by linarith [h₁.1]) hgt (by linarith [h₀.2])
    linarith

/-- **The factor that puts the root at `7/2`** (Sec. VI): the count divided by `c` has its root
at `7/2` exactly when `ln c = ln L · g(7/2) = ln √L + ln C(7/2)`, that is `c = √L · C(7/2)`, and by
the convexity bounds at `3/2`, `−ln 2π ≤ ln C(7/2) ≤ −(3/2) ln π`: `√L/2π ≤ c ≤ √L/π^{3/2}`. -/
theorem seven_halves_factor (L : ℝ) (hL : 1 < L) :
    Real.log L * g L (7 / 2) = Real.log (Real.sqrt L) + logC (7 / 2) ∧
      -Real.log (2 * π) ≤ logC (7 / 2) ∧ logC (7 / 2) ≤ -(3 / 2) * Real.log π := by
  have hL0 : 0 < Real.log L := Real.log_pos hL
  have hf := f_near_three_halves (ε := 1 / 4) (by norm_num) (by norm_num)
  rw [f_three_halves, show (3 / 2 : ℝ) + 1 / 4 = 7 / 4 by norm_num] at hf
  refine ⟨?_, ?_, ?_⟩
  · unfold g
    rw [Real.log_sqrt (by linarith),
      show Real.log L * (7 / 2 - 3 + logC (7 / 2) / Real.log L)
        = Real.log L / 2 + logC (7 / 2) * (Real.log L / Real.log L) by ring,
      div_self hL0.ne', mul_one]
  · unfold logC
    rw [show (7 / 2 : ℝ) / 2 = 7 / 4 by norm_num, Real.log_mul two_ne_zero pi_pos.ne']
    nlinarith [hf.1, hf.2]
  · unfold logC
    rw [show (7 / 2 : ℝ) / 2 = 7 / 4 by norm_num]
    nlinarith [hf.1, hf.2]

/-- **The factor that puts the root at `5/2`**: the count multiplied by `c` has its root at `5/2`
exactly when `ln c = −ln L · g(5/2) = ln √L − ln C(5/2)`, that is `c = √L/C(5/2)`, and by the
chords of `ln Γ` at `5/4`, `−½ ln π ≤ ln C(5/2) ≤ −½ ln 2`: `√(2L) ≤ c ≤ √(πL)`. -/
theorem five_halves_factor (L : ℝ) (hL : 1 < L) :
    -(Real.log L * g L (5 / 2)) = Real.log (Real.sqrt L) - logC (5 / 2) ∧
      -(Real.log π / 2) ≤ logC (5 / 2) ∧ logC (5 / 2) ≤ -(Real.log 2 / 2) := by
  have hL0 : 0 < Real.log L := Real.log_pos hL
  have hlow := f_ge (x := 5 / 4) (by norm_num)
  have hup : 2 * f (5 / 4) ≤ f (3 / 2) := by
    have h := slope_le (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 5 / 4)
      (by norm_num : (5 / 4 : ℝ) < 3 / 2)
    rw [f_one] at h
    have h1 : (0 : ℝ) < 5 / 4 - 1 := by norm_num
    have h2 : (0 : ℝ) < 3 / 2 - 5 / 4 := by norm_num
    rw [div_le_iff₀ h1, div_mul_eq_mul_div, le_div_iff₀ h2] at h
    linarith
  rw [f_three_halves] at hup
  refine ⟨?_, ?_, ?_⟩
  · unfold g
    rw [Real.log_sqrt (by linarith),
      show Real.log L * (5 / 2 - 3 + logC (5 / 2) / Real.log L)
        = -(Real.log L / 2) + logC (5 / 2) * (Real.log L / Real.log L) by ring,
      div_self hL0.ne', mul_one]
    ring
  · unfold logC
    rw [show (5 / 2 : ℝ) / 2 = 5 / 4 by norm_num]
    nlinarith [hup]
  · unfold logC
    rw [show (5 / 2 : ℝ) / 2 = 5 / 4 by norm_num]
    nlinarith [hlow]

end Root
end Register
