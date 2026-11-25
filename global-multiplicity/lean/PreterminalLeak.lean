import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination

namespace Catenary.PreterminalLeak

/-- The two gain roots obey the same linear restriction if the leak rates agree.
    The two quadratics are the cleared equations for the gain g and the leak h. -/
theorem equal_leaks_force_level (x y A B C D g h : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (gx : A*x^2 + (B-g)*x - 1 = 0)
    (gy : A*y^2 + (B-g)*y - 1 = 0)
    (lx : (1+g*h)*x^2 - C*x - D = 0)
    (ly : (1+g*h)*y^2 - C*y - D = 0) :
    C = D*(g-B) := by
  have px : x * ((D*A-1-g*h)*x + D*(B-g)+C) = 0 := by
    linear_combination D*gx - lx
  have py : y * ((D*A-1-g*h)*y + D*(B-g)+C) = 0 := by
    linear_combination D*gy - ly
  have ex := (mul_eq_zero.mp px).resolve_left hx
  have ey := (mul_eq_zero.mp py).resolve_left hy
  have diff : (D*A-1-g*h)*(x-y) = 0 := by linear_combination ex - ey
  have slope := (mul_eq_zero.mp diff).resolve_right (sub_ne_zero.mpr hxy)
  linear_combination ex - x*slope

/-- If the exceptional-level equation holds, the leak of the first root also
    solves the cleared leak equation at every other gain root. -/
theorem exceptional_level_suffices (x y A B C D g h : ℝ)
    (hx : x ≠ 0) (level : C = D*(g-B))
    (gx : A*x^2 + (B-g)*x - 1 = 0)
    (gy : A*y^2 + (B-g)*y - 1 = 0)
    (lx : (1+g*h)*x^2 - C*x - D = 0) :
    (1+g*h)*y^2 - C*y - D = 0 := by
  have px : (D*A-1-g*h)*x^2 = 0 := by
    linear_combination D*gx - lx - x*level
  have slope := (mul_eq_zero.mp px).resolve_right (pow_ne_zero 2 hx)
  linear_combination D*gy - y^2*slope - y*level

theorem exceptional_level_unique (B C D g₁ g₂ : ℝ)
    (nonzero : C ≠ 0 ∨ D ≠ 0)
    (first : C = D*(g₁-B)) (second : C = D*(g₂-B)) : g₁ = g₂ := by
  have hd : D ≠ 0 := by
    intro hd
    have hc : C = 0 := by simpa [hd] using first
    exact nonzero.elim (fun h => h hc) (fun h => h hd)
  have diff : D*(g₁-g₂) = 0 := by linear_combination second - first
  exact sub_eq_zero.mp ((mul_eq_zero.mp diff).resolve_left hd)

#print axioms equal_leaks_force_level
#print axioms exceptional_level_suffices
#print axioms exceptional_level_unique

end Catenary.PreterminalLeak
