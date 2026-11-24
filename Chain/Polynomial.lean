import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Касательные полиномиальные данные цепи

Все утверждения действуют над произвольным полем. Основная теорема
`exists_common_spectral_root` строит один корень для всех допустимых вариаций.
Она выводит инъективность на полиномиальных данных из тождества конденсации,
ограничения на степени, взаимной простоты и указанного множества корней.
Матричное происхождение этих предпосылок и аналитическое продолжение
параметризации в эту формулировку не входят.
-/

namespace Catenary

open Polynomial

variable {F : Type*} [Field F]

/-- Данные о произведении с обратимым по модулю множителем различают
    представителей степени ниже модуля. -/
theorem bounded_modular_unique {M b x y : F[X]} (hcop : IsCoprime M b)
    (hx : x.degree < M.degree) (hy : y.degree < M.degree)
    (hcongr : M ∣ b * (x - y)) : x = y := by
  apply sub_eq_zero.mp
  exact eq_zero_of_dvd_of_degree_lt (hcop.dvd_of_dvd_mul_left hcongr)
    ((degree_sub_le x y).trans_lt (max_lt hx hy))

/-- Существование и единственность остатка: алгебраический шаг восстановления
    правого хвоста в §4, применимый также к построению общей точки в §5. -/
theorem existsUnique_bounded_modular_solution {M b : F[X]} (w : F[X])
    (hM : M.Monic) (hcop : IsCoprime M b) :
    ∃! x : F[X], x.degree < M.degree ∧ M ∣ b * x - w := by
  obtain ⟨a, c, hbez⟩ := hcop
  let x := (c * w) %ₘ M
  have hx : x.degree < M.degree := degree_modByMonic_lt _ hM
  have hsplit : x + M * ((c * w) /ₘ M) = c * w := modByMonic_add_div _ hM
  have hxmod : M ∣ b * x - w := by
    refine ⟨-a * w - b * ((c * w) /ₘ M), ?_⟩
    linear_combination b * hsplit + w * hbez
  refine ⟨x, ⟨hx, hxmod⟩, ?_⟩
  rintro y ⟨hy, hymod⟩
  apply bounded_modular_unique ⟨a, c, hbez⟩ hy hx
  rw [show b * (y - x) = (b * y - w) - (b * x - w) by ring]
  exact dvd_sub hymod hxmod

/-- Оба касательных тождества §5, в том числе существование и единственность
    полиномиального частного без деления при вычислении в корне. -/
theorem existsUnique_tangent_quotient {D B W H U P dB dH dP : F[X]}
    (hW : W ≠ 0) (hcop : IsCoprime W U)
    (hbase : D * B = W * H - U * P)
    (hdiff : D * dB = W * dH - U * dP) :
    ∃! q : F[X], B * dP - P * dB = W * q ∧ P * dH - H * dP = -(D * q) := by
  have hcross : U * (B * dP - P * dB) = W * (B * dH - H * dB) := by
    linear_combination B * hdiff - dB * hbase
  obtain ⟨q, hq⟩ := hcop.dvd_of_dvd_mul_left ⟨_, hcross⟩
  refine ⟨q, ⟨hq, ?_⟩, ?_⟩
  · apply mul_left_cancel₀ hW
    linear_combination -P * hdiff + dP * hbase - D * hq
  · intro q' hq'
    exact mul_left_cancel₀ hW (hq'.1.symm.trans hq)

/-- Нулевое касательное частное вынуждает обе неизвестные вариации обнулиться. -/
theorem zero_tangent_quotient_kernel {B P dB dP : F[X]}
    (hB : B ≠ 0) (hcop : IsCoprime B P) (hlow : dB.degree < B.degree)
    (hzero : B * dP - P * dB = 0) : dB = 0 ∧ dP = 0 := by
  have hprod := sub_eq_zero.mp hzero
  have hdB := eq_zero_of_dvd_of_degree_lt
    (hcop.dvd_of_dvd_mul_left (show B ∣ P * dB from ⟨dP, hprod.symm⟩)) hlow
  refine ⟨hdB, (mul_eq_zero.mp ?_).resolve_left hB⟩
  simpa only [hdB, mul_zero] using hprod

/-- Без фиксации K степень ненулевого касательного частного ограничена
    суммой deg P + deg B − deg W. Под геометрическим порогом это не выше 1. -/
theorem tangent_quotient_degree_bound {B P W dB dP q : F[X]} (hW : W ≠ 0) (hq0 : q ≠ 0)
    (hdb : dB.degree ≤ B.degree) (hdp : dP.degree ≤ P.degree)
    (hq : B * dP - P * dB = W * q) :
    W.natDegree + q.natDegree ≤ P.natDegree + B.natDegree := by
  have hb := natDegree_le_natDegree hdb
  have hp := natDegree_le_natDegree hdp
  have hleft : (B * dP).natDegree ≤ B.natDegree + dP.natDegree := natDegree_mul_le
  have hright : (P * dB).natDegree ≤ P.natDegree + dB.natDegree := natDegree_mul_le
  have h := natDegree_sub_le (B * dP) (P * dB)
  rw [hq, natDegree_mul hW hq0] at h
  exact h.trans (max_le (by omega) (by omega))

/-- При пороге d ≤ r + 2 и δK = 0 касательное частное постоянно.
    Геометрический порог записан как deg P + deg B ≤ deg W + 1. -/
theorem tangent_quotient_constant {B P W dB dP q : F[X]} (hW : W ≠ 0)
    (hdb : dB.degree < B.degree) (hdp : dP.degree < P.degree)
    (hlen : P.natDegree + B.natDegree ≤ W.natDegree + 1)
    (hq : B * dP - P * dB = W * q) : q.natDegree = 0 := by
  by_cases hq0 : q = 0
  · simp [hq0]
  have hleft : (B * dP).natDegree ≤ W.natDegree := by
    by_cases h : dP = 0
    · simp [h]
    have hlt := natDegree_lt_natDegree h hdp
    have hmul : (B * dP).natDegree ≤ B.natDegree + dP.natDegree := natDegree_mul_le
    omega
  have hright : (P * dB).natDegree ≤ W.natDegree := by
    by_cases h : dB = 0
    · simp [h]
    have hlt := natDegree_lt_natDegree h hdb
    have hmul : (P * dB).natDegree ≤ P.natDegree + dB.natDegree := natDegree_mul_le
    omega
  have h := (natDegree_sub_le (B * dP) (P * dB)).trans (max_le hleft hright)
  rw [hq, natDegree_mul hW hq0] at h
  omega

/-- При P=K E и постоянном касательном частном c неизвестная вариация δP
    равна cR, где единый остаток R определяется только исходными данными. -/
theorem tangent_multiple_of_residue {E B W P R dB dP : F[X]} {k c : F}
    (hcop : IsCoprime E B) (hp : P = C k * E)
    (hRlow : R.degree < E.degree) (hRmod : E ∣ B * R - W)
    (hdP : dP.degree < E.degree) (hq : B * dP - P * dB = W * C c) :
    dP = C c * R := by
  obtain ⟨t, ht⟩ := hRmod
  have hlow : (C c * R).degree < E.degree := by
    by_cases hc : c = 0
    · rw [hc, map_zero, zero_mul]
      exact (show (0 : F[X]).degree ≤ R.degree by simp).trans_lt hRlow
    · rwa [degree_C_mul hc]
  apply bounded_modular_unique hcop hdP hlow
  refine ⟨C k * dB - C c * t, ?_⟩
  rw [hp] at hq
  linear_combination hq - C c * ht

/-- Полиномиальные компоненты произвольной касательной вариации при
    фиксированных D, W, U. Условия степеней включают нулевые вариации
    монических многочленов степени нуль. -/
structure SpectralVariation (D B W U P E : F[X]) (k : F) where
  dB : F[X]
  dP : F[X]
  dH : F[X]
  dE : F[X]
  dK : F
  degB : dB.degree < B.degree
  degE : dE.degree < E.degree
  product_rule : dP = C k * dE + C dK * E
  condensation : D * dB = W * dH - U * dP

/-- Общая спектральная точка в §5. Один x из заданного множества корней D
    с ненулевыми E,H аннулирует совместное ядро выбранных двух измерений во
    всём классе полиномиальных вариаций. Выбор x не зависит от вариации. -/
theorem exists_common_spectral_root {D B W H U P E : F[X]} {k : F}
    (hk : k ≠ 0) (hp : P = C k * E) (hE : E.Monic) (hEpos : 0 < E.natDegree)
    (hW : W ≠ 0) (hWU : IsCoprime W U) (hEB : IsCoprime E B) (hEW : IsCoprime E W)
    (hbase : D * B = W * H - U * P)
    (hlen : P.natDegree + B.natDegree ≤ W.natDegree + 1)
    (s : Finset F) (hcard : E.natDegree ≤ s.card)
    (hs : ∀ x ∈ s, D.eval x = 0 ∧ E.eval x ≠ 0 ∧ H.eval x ≠ 0) :
    ∃ x ∈ s, ∀ v : SpectralVariation D B W U P E k,
      v.dE.eval x = 0 → v.dH.eval x = 0 →
        v.dK = 0 ∧ v.dB = 0 ∧ v.dP = 0 ∧ v.dH = 0 ∧ v.dE = 0 := by
  classical
  obtain ⟨R, ⟨hRlow, hRmod⟩, _⟩ := existsUnique_bounded_modular_solution W hE hEB
  have hR : R ≠ 0 := by
    intro hr
    have hdvd : E ∣ W := by simpa [hr] using hRmod
    have hunit : E ∣ (1 : F[X]) :=
      hEW.dvd_of_dvd_mul_left (by simpa only [mul_one] using hdvd : E ∣ W * 1)
    have hle := natDegree_le_of_dvd hunit one_ne_zero
    simp only [natDegree_one] at hle
    omega
  have hRcard := (natDegree_lt_natDegree hR hRlow).trans_le hcard
  obtain ⟨x, hx, hxR⟩ : ∃ x ∈ s, R.eval x ≠ 0 := by
    by_contra! h
    exact hR (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R s h hRcard)
  obtain ⟨hxD, hxE, hxH⟩ := hs x hx
  refine ⟨x, hx, ?_⟩
  intro v he hh
  obtain ⟨q, ⟨hq, hq2⟩, _⟩ := existsUnique_tangent_quotient hW hWU hbase v.condensation
  have hpEval : v.dP.eval x = 0 := by
    have hev := congrArg (fun f : F[X] => f.eval x) hq2
    have hmul : H.eval x * v.dP.eval x = 0 := by
      simpa only [eval_sub, eval_mul, eval_neg, hh, hxD, mul_zero, zero_mul,
        zero_sub, neg_zero, neg_eq_zero] using hev
    exact (mul_eq_zero.mp hmul).resolve_left hxH
  have hk0 : v.dK = 0 := by
    have hev := congrArg (fun f : F[X] => f.eval x) v.product_rule
    have hmul : 0 = v.dK * E.eval x := by
      simpa only [eval_add, eval_mul, eval_C, hpEval, he, mul_zero, zero_add] using hev
    exact (mul_eq_zero.mp hmul.symm).resolve_right hxE
  have hprod : v.dP = C k * v.dE := by
    simpa only [hk0, map_zero, zero_mul, add_zero] using v.product_rule
  have hpLowE : v.dP.degree < E.degree := by
    rw [hprod, degree_C_mul hk]
    exact v.degE
  have hpLowP : v.dP.degree < P.degree := by
    exact hpLowE.trans_eq ((congrArg Polynomial.degree hp).trans (degree_C_mul hk)).symm
  let c := q.coeff 0
  have hqc : q = C c :=
    eq_C_of_natDegree_eq_zero (tangent_quotient_constant hW v.degB hpLowP hlen hq)
  have hconst : B * v.dP - P * v.dB = W * C c := hq.trans (congrArg (W * ·) hqc)
  have hdP := tangent_multiple_of_residue hEB hp hRlow hRmod hpLowE hconst
  have hc : c = 0 := by
    have hev := congrArg (fun f : F[X] => f.eval x) hdP
    have hmul : 0 = c * R.eval x := by
      simpa only [hpEval, eval_mul, eval_C] using hev
    exact (mul_eq_zero.mp hmul.symm).resolve_right hxR
  have hdP0 : v.dP = 0 := by simpa only [hc, map_zero, zero_mul] using hdP
  have hpNe : P ≠ 0 := by
    rw [hp]
    exact mul_ne_zero (C_ne_zero.mpr hk) hE.ne_zero
  have hdB0 : v.dB = 0 := by
    have hmul : P * v.dB = 0 := by
      simpa only [hdP0, mul_zero, zero_sub, hc, map_zero, neg_eq_zero] using hconst
    exact (mul_eq_zero.mp hmul).resolve_left hpNe
  have hdH0 : v.dH = 0 := by
    have hmul : 0 = W * v.dH := by
      simpa only [hdB0, hdP0, mul_zero, sub_zero] using v.condensation
    exact (mul_eq_zero.mp hmul.symm).resolve_left hW
  have hdE0 : v.dE = 0 := by
    have hmul : 0 = C k * v.dE := by simpa only [hdP0] using hprod
    exact (mul_eq_zero.mp hmul.symm).resolve_left (C_ne_zero.mpr hk)
  exact ⟨hk0, hdB0, hdP0, hdH0, hdE0⟩

/-- Если разность числителя Y и QL кратна D, первая вариация дроби Y/Q
    в неподвижном корне D совпадает с вариацией L. Формулы использованы
    в дополнительном алгебраическом доказательстве §6. -/
theorem gain_quotient_derivative_at_root
    {D Q L A Y dD dQ dL dA dY : F[X]} (x : F) (hQ : Q.eval x ≠ 0)
    (hD : D.eval x = 0) (hdD : dD.eval x = 0)
    (hbase : Y = Q * L + D * A)
    (hder : dY = dQ * L + Q * dL + dD * A + D * dA) :
    (dY.eval x * Q.eval x - Y.eval x * dQ.eval x) / Q.eval x ^ 2 = dL.eval x := by
  rw [hbase, hder]
  simp only [eval_add, eval_mul, hD, hdD, zero_mul, add_zero]
  apply (div_eq_iff (pow_ne_zero 2 hQ)).2
  ring

/-- Ненулевой рациональный минор допускает сколь угодно большой положительный
    аргумент с ненулевым знаменателем. Опорная точка x может иметь любой знак. -/
theorem rational_minor_above [LinearOrder F] [NoMaxOrder F]
    (p q : F[X]) (x bound : F) (h : p.eval x / q.eval x ≠ 0) :
    ∃ z, bound < z ∧ q.eval z ≠ 0 ∧ p.eval z / q.eval z ≠ 0 := by
  classical
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at h
  have hq : q ≠ 0 := by
    intro hq
    simp [hq] at h
  obtain ⟨z, hz, he⟩ : ∃ z ∈ Set.Ioi bound, (p * q).eval z ≠ 0 := by
    by_contra! hzero
    apply mul_ne_zero hp hq
    apply eq_zero_of_infinite_isRoot
    exact (Set.Ioi_infinite bound).mono (fun z hz => hzero z hz)
  have hn : p.eval z ≠ 0 ∧ q.eval z ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [eval_mul] using he)
  exact ⟨z, hz, hn.2, div_ne_zero hn.1 hn.2⟩

/-- Присоединение префикса при V=0 в §7. Взаимной простоты достаточно
    даже без предположения о расщеплении характеристического многочлена. -/
theorem prefix_tangent_kernel {S R dV dTail : F[X]} (hS : S ≠ 0)
    (hcop : IsCoprime S R) (hdV : dV.degree < S.degree)
    (h : S * dTail = dV * R) : dV = 0 ∧ dTail = 0 := by
  have hdvd : S ∣ dV * R := ⟨dTail, h.symm⟩
  have hv := eq_zero_of_dvd_of_degree_lt (hcop.dvd_of_dvd_mul_right hdvd) hdV
  refine ⟨hv, (mul_eq_zero.mp ?_).resolve_left hS⟩
  simpa only [hv, zero_mul] using h

/-- Вариант шага с префиксом непосредственно в терминах различных корней S
    и значений R на них, как в доказательстве рукописи. -/
theorem prefix_tangent_kernel_of_roots {S R dV dTail : F[X]} (hS : S ≠ 0)
    (s : Finset F) (hcard : dV.natDegree < s.card)
    (hs : ∀ x ∈ s, S.eval x = 0 ∧ R.eval x ≠ 0)
    (h : S * dTail = dV * R) : dV = 0 ∧ dTail = 0 := by
  have hv := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' dV s (by
    intro x hx
    obtain ⟨hsx, hrx⟩ := hs x hx
    have hev := congrArg (fun f : F[X] => f.eval x) h
    have hmul : 0 = dV.eval x * R.eval x := by
      simpa only [eval_mul, hsx, zero_mul] using hev
    exact (mul_eq_zero.mp hmul.symm).resolve_right hrx) hcard
  refine ⟨hv, (mul_eq_zero.mp ?_).resolve_left hS⟩
  simpa only [hv, zero_mul] using h

end Catenary
