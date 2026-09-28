import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The offsets: Sec. IV of *The Dimension of Space from the Granularity of Hilbert Space* (v16-34)

Each cell has its own zero mark for phase (Postulate 1), and a move from cell `a` to cell `b` adds
to the phase an amount that belongs to the pair, their offset.  Phase comes in whole notches, so
offsets, marks and their sums live in `ZMod L`.  A path is the list of cells visited in order, and
its sum is the sum of the offsets of its steps.  This file proves the four facts about offsets that
Sec. IV uses, on any set of cells:

* `pathSum_coboundary`, `closed_coboundary`: the offsets that a choice of marks induces,
  `o(a, b) = m(b) − m(a)`, sum to the difference of the marks at the ends of a path, so to zero
  around a closed path.
* `closed_sum_invariant`: the sum of the offsets around a closed path is the same for every choice
  of marks.
* `no_single_offset`: no choice of marks changes one offset alone: on a closed path through the
  pair on which the other offsets are unchanged, the offset of the pair is unchanged too.
* `quantum_changes_closed_sum`: passing one notch to the offset of a pair changes the sum along
  every path that steps through the pair once, closed paths included.
* `ring_offsets`: on one ring, with cells `0, …, n` and the step from `n` back to `0`, two
  assignments of offsets with the same total differ by a choice of marks, so the only datum in the
  offsets of one ring is their total.  The modulus `L` of the offsets and the number `n + 1` of
  cells are independent here; in the register both are `L`.  Together with `closed_sum_invariant`, which keeps that total
  fixed, this is the sentence of Sec. IV: on one ring the offsets hold one number, which belongs to
  no place, and cannot be a leg.
-/

open Finset

namespace Register
namespace Offsets

variable {Cell : Type*} {L : ℕ}

/-- the offsets that a choice of marks `m` induces: a move from `a` to `b` adds `m b − m a` -/
def coboundary (m : Cell → ZMod L) : Cell → Cell → ZMod L := fun a b => m b - m a

/-- the sum of the offsets `o` along a path, the list of cells visited in order -/
def pathSum (o : Cell → Cell → ZMod L) : List Cell → ZMod L
  | [] => 0
  | [_] => 0
  | a :: b :: rest => o a b + pathSum o (b :: rest)

@[simp] lemma pathSum_nil (o : Cell → Cell → ZMod L) : pathSum o [] = 0 := rfl

@[simp] lemma pathSum_single (o : Cell → Cell → ZMod L) (a : Cell) : pathSum o [a] = 0 := rfl

@[simp] lemma pathSum_cons_cons (o : Cell → Cell → ZMod L) (a b : Cell) (rest : List Cell) :
    pathSum o (a :: b :: rest) = o a b + pathSum o (b :: rest) := rfl

/-- **The offsets of a choice of marks sum to the difference of the marks at the ends of the
path.** -/
theorem pathSum_coboundary (m : Cell → ZMod L) :
    ∀ (p : List Cell) (a : Cell),
      pathSum (coboundary m) (a :: p) = m ((a :: p).getLast (List.cons_ne_nil a p)) - m a
  | [], a => by simp
  | b :: q, a => by
      rw [pathSum_cons_cons, pathSum_coboundary m q b, List.getLast_cons (List.cons_ne_nil b q)]
      simp only [coboundary]
      ring

/-- **Around a closed path the offsets of a choice of marks sum to zero** (Sec. IV): every cell on
the path is entered once and left once. -/
theorem closed_coboundary (m : Cell → ZMod L) (p : List Cell) (a : Cell)
    (hclosed : (a :: p).getLast (List.cons_ne_nil a p) = a) :
    pathSum (coboundary m) (a :: p) = 0 := by
  rw [pathSum_coboundary, hclosed, sub_self]

/-- offsets added pointwise -/
def add (o o' : Cell → Cell → ZMod L) : Cell → Cell → ZMod L := fun a b => o a b + o' a b

theorem pathSum_add (o o' : Cell → Cell → ZMod L) :
    ∀ p : List Cell, pathSum (add o o') p = pathSum o p + pathSum o' p
  | [] => by simp
  | [a] => by simp
  | a :: b :: rest => by
      rw [pathSum_cons_cons, pathSum_cons_cons, pathSum_cons_cons, pathSum_add o o' (b :: rest)]
      simp only [add]
      ring

/-- **The sum of the offsets around a closed path is the same for every choice of marks**
(Sec. IV). -/
theorem closed_sum_invariant (o : Cell → Cell → ZMod L) (m : Cell → ZMod L) (p : List Cell)
    (a : Cell) (hclosed : (a :: p).getLast (List.cons_ne_nil a p) = a) :
    pathSum (add o (coboundary m)) (a :: p) = pathSum o (a :: p) := by
  rw [pathSum_add, closed_coboundary m p a hclosed, add_zero]

/-- **No choice of marks changes one offset alone** (Sec. IV): on a closed path `a, b, …, a` on
which the marks change none of the offsets after the first step, they do not change the offset of
the pair `(a, b)` either. -/
theorem no_single_offset (m : Cell → ZMod L) (a b : Cell) (q : List Cell)
    (hclosed : (a :: b :: q).getLast (List.cons_ne_nil a (b :: q)) = a)
    (hrest : pathSum (coboundary m) (b :: q) = 0) : coboundary m a b = 0 := by
  have h := closed_coboundary m (b :: q) a hclosed
  rw [pathSum_cons_cons, hrest, add_zero] at h
  exact h

variable [DecidableEq Cell]

/-- one notch `c` passed to the offset of the pair `(a, b)`: the offset from `a` to `b` rises by
`c`, the offset from `b` to `a` falls by `c`, and nothing else changes -/
def bump (c : ZMod L) (a b : Cell) : Cell → Cell → ZMod L :=
  fun x y => if x = a ∧ y = b then c else if x = b ∧ y = a then -c else 0

/-- a path that never steps from `a` to `b` or from `b` to `a` -/
def avoids (a b : Cell) : List Cell → Prop
  | x :: y :: rest => ¬(x = a ∧ y = b) ∧ ¬(x = b ∧ y = a) ∧ avoids a b (y :: rest)
  | _ => True

theorem pathSum_bump_of_avoids (c : ZMod L) (a b : Cell) :
    ∀ p : List Cell, avoids a b p → pathSum (bump c a b) p = 0
  | [], _ => by simp
  | [_], _ => by simp
  | x :: y :: rest, h => by
      obtain ⟨h1, h2, h3⟩ := h
      rw [pathSum_cons_cons, pathSum_bump_of_avoids c a b (y :: rest) h3]
      simp [bump, h1, h2]

/-- **A quantum changes the sum around every closed path through its pair** (Sec. IV): on any
path, closed or not, that steps from `a` to `b` once and otherwise avoids the pair, one notch
passed to the offset of the pair raises the sum by one notch. -/
theorem quantum_changes_closed_sum (o : Cell → Cell → ZMod L) (c : ZMod L) (a b : Cell)
    (q : List Cell) (h : avoids a b (b :: q)) :
    pathSum (add o (bump c a b)) (a :: b :: q) = pathSum o (a :: b :: q) + c := by
  rw [pathSum_add, pathSum_cons_cons (bump c a b), pathSum_bump_of_avoids c a b (b :: q) h]
  simp [bump]

/-- **On one ring the offsets hold one number** (Sec. IV).  With cells `0, …, n` in order and the
step from `n` back to `0`, let `o i` be the offset of the step from cell `i` to the next.  Two
assignments of offsets with the same total differ by a choice of marks: their difference is
`m(i + 1) − m(i)` on every step, the wrap included.  So the only datum in the offsets of one ring
is their total, which `closed_sum_invariant` keeps fixed.  The offsets live in `ZMod L` for any
`L`, and the ring has `n + 1` cells for any `n`; in the register both are `L`. -/
theorem ring_offsets (n : ℕ) (o o' : ℕ → ZMod L)
    (htot : ∑ k ∈ range (n + 1), o' k = ∑ k ∈ range (n + 1), o k) :
    ∃ m : ℕ → ZMod L, (∀ i, i < n → o' i - o i = m (i + 1) - m i) ∧
      o' n - o n = m 0 - m n := by
  refine ⟨fun i => ∑ k ∈ range i, (o' k - o k), ?_, ?_⟩
  · intro i _
    simp only [Finset.sum_range_succ]
    ring
  · have hsplit := Finset.sum_range_succ (fun k => o' k - o k) n
    have hzero : ∑ k ∈ range (n + 1), (o' k - o k) = 0 := by
      rw [Finset.sum_sub_distrib, htot, sub_self]
    rw [hzero] at hsplit
    simp only [Finset.sum_range_zero]
    linear_combination (-1 : ZMod L) * hsplit

end Offsets
end Register
