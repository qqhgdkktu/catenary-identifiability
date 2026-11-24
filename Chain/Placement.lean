import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace Catenary

/-- Positions are the one-based chamber numbers used in the manuscript.
Writing both inequalities without subtraction makes the expression valid in Nat. -/
def placement (n i j k : Nat) : Prop :=
  j + k ≤ n + i + 2 ∧ i ≤ j + k + 1

theorem placement_int (n i j k : Nat) :
    placement n i j k ↔
    (j : Int) + k - n - 2 ≤ i ∧ (i : Int) ≤ j + k + 1 := by
  unfold placement
  omega

theorem placement_left {n i j k : Nat} (hi : i < j) (hk : k ≤ n) :
    placement n i j k ↔ j - i ≤ n - k + 2 := by
  unfold placement
  omega

theorem placement_middle {n i j k : Nat} (hji : j ≤ i) (hik : i ≤ k) (hk : k ≤ n) :
    placement n i j k := by
  unfold placement
  omega

theorem placement_right {n i j k : Nat} (hjk : j ≤ k) (hki : k < i) (hi : i ≤ n) :
    placement n i j k ↔ i - k ≤ j + 1 := by
  unfold placement
  omega

theorem placement_reflect {n i j k : Nat} (hi : i ≤ n) (hj : j ≤ n) (hk : k ≤ n) :
    placement n (n+1-i) (n+1-k) (n+1-j) ↔ placement n i j k := by
  unfold placement
  omega

theorem near_output {n i j k : Nat} (hk : k ≤ n) (hjk : j < k)
    (h : (i ≤ j+1 ∧ j ≤ i+1) ∨ (i ≤ k+1 ∧ k ≤ i+1)) :
    placement n i j k := by
  unfold placement
  omega

/-- Coefficient count in §2 for an inlet to the left of both outputs. -/
theorem left_deficit_iff {n i j k : Nat} (hpos : 1 ≤ i) (hij : i < j)
    (hjk : j < k) (hkn : k ≤ n) :
    n + (i-1) + (n-j) + (n-k) + 2 < 2*n-1 ↔ ¬ placement n i j k := by
  unfold placement
  omega

example : placement 4 1 3 4 := by unfold placement; decide
example : placement 7 1 4 6 := by unfold placement; decide
example : ¬ placement 7 1 4 7 := by unfold placement; decide

end Catenary
