import Chain.Continuant
import Chain.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Алгебраический критерий для характеристических многочленов одной цепи

Здесь D, B, W, H, U, E строятся из действительных матричных блоков над полем.
Тождество конденсации и их степени следуют из определения, включая пустой
средний и правый блоки. Предположения о спектре и взаимной простоте указаны
явно. Вывод относится к полиномиальным касательным данным.
-/

namespace Catenary

open Polynomial Continuant

/-- Характеристический многочлен матрицы одного интервала цепи. -/
noncomputable abbrev intervalCharpoly {R : Type*} [CommRing R] (xs : List (PathSite R)) : R[X] :=
  (pathMatrix xs).charpoly

theorem intervalCharpoly_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    (xs : List (PathSite R)) :
    (intervalCharpoly xs).natDegree = xs.length := by
  simp only [intervalCharpoly, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

variable {F : Type*} [Field F]

/-- Концевой вход, два отмеченных выхода j и k и геометрический порог §4.
    После выбора x обе оценки полиномов различают все допустимые вариации.
    Тождество D B = W H − U P и ограничение степеней доказаны для самой цепи. -/
theorem chain_common_spectral_root (left middle right : List (PathSite F))
    (j k : PathSite F) (s : Finset F)
    (hleft : 0 < left.length) (hthreshold : left.length ≤ right.length + 2)
    (hcard : left.length ≤ s.card)
    (hk : j.weight * edgeProduct middle ≠ 0)
    (hWU : IsCoprime (intervalCharpoly (middle ++ k :: right)) (intervalCharpoly right))
    (hEB : IsCoprime (intervalCharpoly left) (intervalCharpoly middle))
    (hEW : IsCoprime (intervalCharpoly left) (intervalCharpoly (middle ++ k :: right)))
    (hs : ∀ x ∈ s, (intervalCharpoly (left ++ j :: (middle ++ k :: right))).eval x = 0 ∧
      (intervalCharpoly left).eval x ≠ 0 ∧ (intervalCharpoly (left ++ j :: middle)).eval x ≠ 0) :
    let D := intervalCharpoly (left ++ j :: (middle ++ k :: right))
    let B := intervalCharpoly middle
    let W := intervalCharpoly (middle ++ k :: right)
    let U := intervalCharpoly right
    let E := intervalCharpoly left
    let K := j.weight * edgeProduct middle
    ∃ x ∈ s, ∀ v : SpectralVariation D B W U (C K * E) E K,
      v.dE.eval x = 0 → v.dH.eval x = 0 →
        v.dK = 0 ∧ v.dB = 0 ∧ v.dP = 0 ∧ v.dH = 0 ∧ v.dE = 0 := by
  dsimp only
  apply exists_common_spectral_root hk rfl (Matrix.charpoly_monic _)
    _ (Matrix.charpoly_monic _).ne_zero hWU hEB hEW
    (charpoly_condensation left middle right j k) _ s _ hs
  · rwa [intervalCharpoly_natDegree]
  · rw [natDegree_C_mul hk]
    simp only [intervalCharpoly_natDegree, List.length_append, List.length_cons]
    omega
  · rwa [intervalCharpoly_natDegree]

end Catenary
