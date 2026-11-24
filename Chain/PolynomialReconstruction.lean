import Chain.PolynomialChain
import Mathlib.Algebra.DualNumber

/-!
# Восстановление интервального блока по двум характеристическим многочленам

Параметры блока — его диагонали и произведения встречных скоростей β на
рёбрах. При вычислении определителей каждое ребро можно представить
верхним элементом β и нижним элементом 1. Обратимость β позволяет работать
над произвольным ненулевым коммутативным кольцом, включая двойственные числа.
-/

namespace Catenary

open Polynomial Continuant

variable {R : Type*} [CommRing R]

/-- Блок с n рёбрами и n+1 диагональными элементами. -/
inductive JacobiData (R : Type*) [CommRing R] : ℕ → Type _
  | single (a : R) : JacobiData R 0
  | extend {n} (a : R) (b : Rˣ) (t : JacobiData R n) : JacobiData R (n + 1)

namespace JacobiData

def sites {n : ℕ} : JacobiData R n → List (PathSite R)
  | .single a => [⟨a, 0, 0⟩]
  | .extend a b t => ⟨a, b, 1⟩ :: t.sites

theorem sites_length {n} (t : JacobiData R n) : t.sites.length = n + 1 := by
  induction t with
  | single => rfl
  | extend a b t ih => simp only [sites, List.length_cons, ih]

theorem tail_length {n} (t : JacobiData R n) : t.sites.tail.length = n := by
  cases t with
  | single => rfl
  | extend a b t => exact t.sites_length

/-- Оба полинома — характеристические многочлены фактических матриц. -/
noncomputable def boundaryPair {n} (t : JacobiData R n) : R[X] × R[X] :=
  (intervalCharpoly t.sites, intervalCharpoly t.sites.tail)

theorem boundaryPair_single (a : R) : (single a).boundaryPair.1 = X - C a := by
  change (pathMatrix [⟨a, 0, 0⟩]).charpoly = X - C a
  exact (charpoly_eq_cont _).trans (cont_singleton _)

private theorem interval_cons_cons (a b : PathSite R) (t : List (PathSite R)) :
    intervalCharpoly (a :: b :: t) =
      (X - C a.diag) * intervalCharpoly (b :: t) - C a.weight * intervalCharpoly t := by
  simp only [intervalCharpoly, charpoly_eq_cont, List.map_cons, cont_cons_cons, pencil_weight]
  rfl

theorem boundaryPair_extend {n} (a : R) (b : Rˣ) (t : JacobiData R n) :
    (extend a b t).boundaryPair.1 =
      (X - C a) * t.boundaryPair.1 - C (b : R) * t.boundaryPair.2 := by
  cases t <;> simp only [boundaryPair, sites, List.tail_cons, interval_cons_cons,
    PathSite.weight, mul_one]

/-- Два последовательных концевых определителя взаимно просты при обратимых
    рёбрах. Никакой гипотезы о корнях матрицы здесь не требуется. -/
theorem consecutive_coprime {n} (t : JacobiData R n) :
    IsCoprime t.boundaryPair.1 t.boundaryPair.2 := by
  induction t with
  | single a =>
    have h : (single a).boundaryPair.2 = 1 := by
      exact (charpoly_eq_cont ([] : List (PathSite R))).trans cont_nil
    rw [h]
    exact isCoprime_one_right
  | extend a b t ih =>
    obtain ⟨u, v, hbez⟩ := ih
    change IsCoprime (extend a b t).boundaryPair.1 t.boundaryPair.1
    rw [boundaryPair_extend]
    have hu : (C ((b⁻¹ : Rˣ) : R) : R[X]) * C (b : R) = 1 := by
      rw [← map_mul]
      simp
    refine ⟨-v * C ((b⁻¹ : Rˣ) : R),
      u + v * C ((b⁻¹ : Rˣ) : R) * (X - C a), ?_⟩
    calc
      _ = u * t.boundaryPair.1 +
        v * (C ((b⁻¹ : Rˣ) : R) * C (b : R)) * t.boundaryPair.2 := by ring
      _ = 1 := by simpa only [hu, mul_one] using hbez

variable [Nontrivial R]

theorem boundary_degree {n} (t : JacobiData R n) :
    t.boundaryPair.2.degree < t.boundaryPair.1.degree := by
  change (intervalCharpoly t.sites.tail).degree < (intervalCharpoly t.sites).degree
  rw [degree_eq_natDegree (Matrix.charpoly_monic _).ne_zero,
    degree_eq_natDegree (Matrix.charpoly_monic _).ne_zero,
    intervalCharpoly_natDegree, intervalCharpoly_natDegree, sites_length, tail_length]
  exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n)

/-- Частное возвращает диагональ, а остаток — следующий полином, умноженный
    на отрицательный вес ребра. -/
theorem boundary_division {n} (a : R) (b : Rˣ) (t : JacobiData R n) :
    (extend a b t).boundaryPair.1 /ₘ t.boundaryPair.1 = X - C a ∧
    (extend a b t).boundaryPair.1 %ₘ t.boundaryPair.1 = -(C (b : R) * t.boundaryPair.2) := by
  apply div_modByMonic_unique _ _ (Matrix.charpoly_monic _)
  constructor
  · change -(C (b : R) * t.boundaryPair.2) + t.boundaryPair.1 * (X - C a) =
      (extend a b t).boundaryPair.1
    rw [boundaryPair_extend]
    ring
  · rw [degree_neg, degree_C_mul_of_isUnit b.isUnit]
    exact t.boundary_degree

/-- Два последовательных определителя однозначно определяют все диагонали
    и все β блока произвольной фиксированной длины. Результат справедлив
    также для кольца с нильпотентами при обратимых весах. -/
theorem boundaryPair_injective (n : ℕ) :
    Function.Injective (boundaryPair (R := R) (n := n)) := by
  induction n with
  | zero =>
    intro u v huv
    cases u with
    | single a =>
      cases v with
      | single a' =>
        have he : (X : R[X]) - C a = X - C a' := by
          simpa only [boundaryPair_single] using congrArg Prod.fst huv
        have h : a = a' := C_injective (by linear_combination -he)
        rw [h]
  | succ n ih =>
    intro u v huv
    cases u with
    | extend a b t =>
      cases v with
      | extend a' b' t' =>
        have hfull := congrArg Prod.fst huv
        have htail : t.boundaryPair.1 = t'.boundaryPair.1 := congrArg Prod.snd huv
        obtain ⟨hq, hr⟩ := boundary_division a b t
        obtain ⟨hq', hr'⟩ := boundary_division a' b' t'
        have he : (X : R[X]) - C a = X - C a' := by
          calc
            _ = (extend a b t).boundaryPair.1 /ₘ t.boundaryPair.1 := hq.symm
            _ = (extend a' b' t').boundaryPair.1 /ₘ t'.boundaryPair.1 := by rw [hfull, htail]
            _ = _ := hq'
        have ha : a = a' := C_injective (by linear_combination -he)
        have hrem : -(C (b : R) * t.boundaryPair.2) = -(C (b' : R) * t'.boundaryPair.2) := by
          calc
            _ = (extend a b t).boundaryPair.1 %ₘ t.boundaryPair.1 := hr.symm
            _ = (extend a' b' t').boundaryPair.1 %ₘ t'.boundaryPair.1 := by rw [hfull, htail]
            _ = _ := hr'
        have hprod := neg_inj.mp hrem
        have hm : t.boundaryPair.2.Monic := Matrix.charpoly_monic _
        have hm' : t'.boundaryPair.2.Monic := Matrix.charpoly_monic _
        have hb : b = b' := by
          apply Units.ext
          simpa only [leadingCoeff_C_mul_of_isUnit b.isUnit, leadingCoeff_C_mul_of_isUnit b'.isUnit,
            hm.leadingCoeff, hm'.leadingCoeff, mul_one] using congrArg leadingCoeff hprod
        subst b'
        have hlower := (b.isUnit.map (C : R →+* R[X])).mul_left_cancel hprod
        have ht : t = t' := ih (Prod.ext htail hlower)
        rw [ha, ht]

/-- Специализация на парах «значение + первая вариация·ε», ε²=0. -/
theorem dual_boundaryPair_injective (n : ℕ) :
    Function.Injective (boundaryPair (R := DualNumber R) (n := n)) :=
  boundaryPair_injective n

omit [Nontrivial R] in
/-- Любая первая вариация веса с обратимым исходным значением допускается
    в специализации на двойственных числах. -/
theorem dual_edge_isUnit (a da : R) (ha : IsUnit a) :
    IsUnit (show DualNumber R from (a, da)) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha

end JacobiData
end Catenary
