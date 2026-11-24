import Chain.Placement

/-!
The arithmetic in Appendices A/B, *after* the interval matching ranks
for one inlet, two outlets and one leak have been substituted. No theorem
identifying these scores with the physics is assumed in this module.
-/
namespace Catenary.PublishedRule

def inputScore (i ℓ : Int) : Int :=
  if i ≤ ℓ then max 0 (min (2*i-3) (i-1)) else min (2*i-3) (i-1)

def firstScore (x : Int) : Int := max 0 (min (2*x-3) (x-1))

def secondScore (x y : Int) : Int := max 0 (min (2*y-2) (firstScore x + y))

/-- The three branches correspond respectively to ℓ<j, j≤ℓ<k, k≤ℓ. -/
def leftScore (n i j k ℓ : Int) : Int :=
  let x := n+1-k
  let y := n+1-j
  if ℓ < j then inputScore i ℓ + secondScore x y + 1
  else if ℓ < k then firstScore i + (secondScore x y + 1)
  else firstScore i + min (2*y-1) (firstScore x + 1 + y)

theorem score_formula {n i j k ℓ : Int} (hi : 1 ≤ i)
    (hk : j < k) (hn : k ≤ n) (hℓ : 1 ≤ ℓ) :
    leftScore n i j k ℓ = i-1 + (n+1-k) + (n+1-j) := by
  simp only [leftScore,inputScore,secondScore,firstScore]
  split <;> split <;> omega

/-- For an exterior inlet on the left the published score after specialization
gives exactly the one-based criterion printed in the manuscript. -/
theorem left_threshold {n i j k ℓ : Nat} (hi : 1 ≤ i) (hj : i < j)
    (hk : j < k) (hn : k ≤ n) (hℓ : 1 ≤ ℓ) :
    (n : Int)-1 ≤ leftScore n i j k ℓ ↔ placement n i j k := by
  rw [score_formula (by omega) (by omega) (by omega) (by omega)]
  unfold placement
  omega

end Catenary.PublishedRule
