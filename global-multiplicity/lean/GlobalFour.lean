import GlobalPhysical
import Chain.PhysicalInverse
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace Catenary.GlobalMultiplicity.FourAudit
open Polynomial Continuant
open scoped Polynomial
abbrev X4 := Params 3

def e₁ (x : X4) := x 0 + x 1 + x 3 + x 6
def e₀ (x : X4) := x 0 * (x 1 + x 6)
def p (x : X4) := x 0 * x 1
def q (x : X4) := p x * x 2
def head (x : X4) := e₁ x + x 4 + x 2 + x 5
def quad (x : X4) := e₀ x + (x 2 + x 4 + x 5)*e₁ x + x 5*x 4 - x 1*x 4
def constant (x : X4) := x 5*x 4*(e₀ x - p x)
def atPole (x : X4) := -(x 2*x 5)*(x 5^2-x 5*e₁ x+e₀ x)
def invariant (x : X4) := e₀ x + x 5 * x 4

private theorem invariants_of_Fc (x y : X4) (hx : Positive x)
    (H : Four.Fc 1 x = Four.Fc 1 y) :
    p x = p y ∧ x 5 = y 5 ∧ x 2 = y 2 ∧ head x = head y ∧
    quad x = quad y ∧ constant x = constant y ∧ atPole x = atPole y := by
  have coord : ∀ i, Four.Fc 1 x i = Four.Fc 1 y i := congrFun H
  simp_rw [Four.Fc_eq_observations] at coord
  have hp : p x = p y := coord 4
  have hpn : p x ≠ 0 := mul_ne_zero (hx 0).ne' (hx 1).ne'
  have hB : p x * x 5 = p y * y 5 := by
    simpa [p,Four.diagonal] using coord 5
  have hc : p x * x 2 = p y * y 2 := coord 6
  rw [← hp] at hB hc
  have hb' := mul_left_cancel₀ hpn hB
  have hc' := mul_left_cancel₀ hpn hc
  have hv (s : ℝ) : Four.characteristic 1 x s = Four.characteristic 1 y s := by
    rw [Four.characteristic_eq_coefficients,Four.characteristic_eq_coefficients]
    have a : Four.coefficients 1 x 0 = Four.coefficients 1 y 0 := coord 0
    have b : Four.coefficients 1 x 1 = Four.coefficients 1 y 1 := coord 1
    have c : Four.coefficients 1 x 2 = Four.coefficients 1 y 2 := coord 2
    have d : Four.coefficients 1 x 3 = Four.coefficients 1 y 3 := coord 3
    rw [a,b,c,d]
  have ev (v : X4) : Four.characteristic 1 v (-(v 5)) = atPole v := by
    simp (config := {decide := true}) [Four.characteristic,Four.diagonal,atPole,e₁,e₀]
    ring_nf
    simp
  refine ⟨hp,hb',hc',?_,?_,?_,?_⟩
  · have h := coord 0
    simp (config := {decide := true}) [Four.coefficients,Four.diagonal] at h
    unfold head e₁
    linarith only [h]
  · have h := coord 1
    simp (config := {decide := true}) [Four.coefficients,Four.diagonal] at h
    unfold quad e₁ e₀
    linear_combination h
  · have h := hv 0
    simp (config := {decide := true}) [Four.characteristic,Four.diagonal] at h
    unfold constant e₀ p
    linear_combination h
  · rw [← ev,← ev,hb',hv]

private theorem shared (x y : X4) (hx : Positive x) (H : Four.Fc 1 x = Four.Fc 1 y) :
    invariant x = invariant y ∧
    (x 4 = y 4 ∨ x 5 * (x 4 + y 4) = invariant x - p x) := by
  obtain ⟨hp,hB,ha,ht,_,hd,hv⟩ := invariants_of_Fc x y hx H
  unfold head at ht
  unfold atPole at hv
  rw [← hB, ← ha] at ht hv
  have hmul : -(x 2 * x 5) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (hx 2).ne' (hx 5).ne')
  have e := mul_left_cancel₀ hmul hv
  have hh : invariant x = invariant y := by
    unfold invariant
    rw [← hB]
    linear_combination e + x 5 * ht
  refine ⟨hh,?_⟩
  have fact : (x 4-y 4) * ((invariant x - p x) - x 5 * (x 4+y 4)) = 0 := by
    unfold constant at hd
    rw [← hB,← hp] at hd
    have z : x 4*(e₀ x-p x) = y 4*(e₀ y-p x) := by
      apply mul_left_cancel₀ (hx 5).ne'
      simpa only [mul_assoc] using hd
    unfold invariant at hh ⊢
    rw [← hB] at hh
    linear_combination z - y 4 * hh
  rcases mul_eq_zero.mp fact with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h).symm

private theorem recover (x y : X4) (hx : Positive x)
    (H : Four.Fc 1 x = Four.Fc 1 y) (hz : x 4 = y 4) : x = y := by
  obtain ⟨hp,hB,ha,ht,hs,_,_⟩ := invariants_of_Fc x y hx H
  have hi := (shared x y hx H).1
  unfold invariant at hi
  unfold head at ht
  rw [← hB,← hz] at hi
  rw [← hB,← hz,← ha] at ht
  have he₀ : e₀ x = e₀ y := by linarith
  have he₁ : e₁ x = e₁ y := by linarith
  unfold quad at hs
  rw [← he₀,← he₁,← hB,← ha,← hz] at hs
  have h₁ : x 1 = y 1 := mul_right_cancel₀ (hx 4).ne' (by linarith only [hs] : x 1*x 4 = y 1*x 4)
  unfold p at hp
  rw [← h₁] at hp
  have h₀ := mul_right_cancel₀ (hx 1).ne' hp
  unfold e₀ at he₀
  rw [← h₀,← h₁] at he₀
  have h₆ : x 6 = y 6 := add_left_cancel (mul_left_cancel₀ (hx 0).ne' he₀)
  unfold e₁ at he₁
  rw [← h₀,← h₁,← h₆] at he₁
  have h₃ : x 3 = y 3 := by linarith
  funext i
  fin_cases i <;> assumption

/-- Even singular positive solutions are covered by this four-chamber upper bound. -/
theorem no_three (x y z : X4) (hx : Positive x) (hy : Positive y)
    (hxy : Four.Fc 1 x = Four.Fc 1 y) (hxz : Four.Fc 1 x = Four.Fc 1 z) :
    x = y ∨ x = z ∨ y = z := by
  rcases (shared x y hx hxy).2 with same | other
  · exact Or.inl (recover x y hx hxy same)
  rcases (shared x z hx hxz).2 with same | other'
  · exact Or.inr (Or.inl (recover x z hx hxz same))
  have h := mul_left_cancel₀ (hx 5).ne' (other.trans other'.symm)
  exact Or.inr (Or.inr (recover y z hy (hxy.symm.trans hxz) (add_left_cancel h)))

#print axioms no_three
end Catenary.GlobalMultiplicity.FourAudit
