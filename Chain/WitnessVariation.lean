import Chain.SpectralGain
import Chain.Obstruction
import Chain.ThreeBlocks
import Mathlib.Data.Matrix.Rank

/-!
# Вариации полиномиальной цепи и одна общая спектральная точка

Коэффициенты матрицы — многочлены времени. Внешняя переменная характеристического
многочлена — спектральный аргумент. Взятие касательной производится по времени.
-/

namespace Catenary.WitnessVariation

open Polynomial Continuant

variable {F : Type*} [Field F]

abbrev Family (F : Type*) [Field F] := Polynomial (Polynomial F)

/-- Спектральный многочлен в фиксированный момент времени. -/
noncomputable def value (t : F) (p : Family F) : F[X] := p.map (evalRingHom t)

/-- Спектральный многочлен, составленный из производных всех коэффициентов по времени. -/
noncomputable def velocity (t : F) (p : Family F) : F[X] :=
  .ofFinsupp (p.toFinsupp.mapRange (fun c : F[X] => c.derivative.eval t) (by simp))

@[simp] theorem coeff_value (t : F) (p : Family F) (n : ℕ) :
    (value t p).coeff n = (p.coeff n).eval t := coeff_map _ _

@[simp] theorem coeff_velocity (t : F) (p : Family F) (n : ℕ) :
    (velocity t p).coeff n = (p.coeff n).derivative.eval t := rfl

theorem coefficient_hasDerivAt (t : ℝ) (p : Family ℝ) (n : ℕ) :
    HasDerivAt (fun u => (value u p).coeff n) ((velocity t p).coeff n) t := by
  simpa only [coeff_value, coeff_velocity] using (p.coeff n).hasDerivAt t

@[simp] theorem velocity_add (t : F) (p q : Family F) :
    velocity t (p + q) = velocity t p + velocity t q := by ext n; simp

@[simp] theorem velocity_sub (t : F) (p q : Family F) :
    velocity t (p - q) = velocity t p - velocity t q := by ext n; simp

theorem velocity_mul (t : F) (p q : Family F) :
    velocity t (p * q) = velocity t p * value t q + value t p * velocity t q := by
  ext n
  simp only [coeff_velocity, coeff_mul, coeff_add, derivative_sum, eval_finset_sum,
    derivative_mul, eval_add, eval_mul, Finset.sum_add_distrib, coeff_value]

@[simp] theorem velocity_C (t : F) (c : F[X]) :
    velocity t (C c) = C (c.derivative.eval t) := by
  ext n
  by_cases h : n = 0 <;> simp [coeff_C, h]

@[simp] theorem value_C (t : F) (c : F[X]) : value t (C c) = C (c.eval t) := by
  simp [value]

theorem velocity_monomial (t : F) (n : ℕ) (c : F[X]) :
    velocity t (monomial n c) = monomial n (c.derivative.eval t) := by
  ext m
  by_cases h : n = m <;> simp [coeff_monomial, h]

/-- Моничность даёт строгое ограничение степени даже для постоянного семейства 1. -/
theorem degree_velocity_lt (t : F) {p : Family F} (hp : p.Monic) :
    (velocity t p).degree < (value t p).degree := by
  rw [value, hp.degree_map, degree_eq_natDegree hp.ne_zero, degree_lt_iff_coeff_zero]
  intro n hn
  by_cases he : n = p.natDegree
  · subst n
    simp [hp.coeff_natDegree]
  · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne hn (Ne.symm he))]

/-- Многочлен времени при фиксированном спектральном аргументе. -/
noncomputable def slice (z : F) (p : Family F) : F[X] := p.eval (C z)

theorem velocity_eval (t z : F) (p : Family F) :
    (velocity t p).eval z = (slice z p).derivative.eval t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [slice, hp, hq]
  | monomial n c =>
    simp [slice, velocity_monomial, eval_monomial, ← map_pow, derivative_mul]

theorem slice_hasDerivAt (t z : ℝ) (p : Family ℝ) :
    HasDerivAt (fun u => (slice z p).eval u) ((velocity t p).eval z) t :=
  (velocity_eval t z p).symm ▸ (slice z p).hasDerivAt t

/-- Полиномиальная траектория всех узлов и ориентированных рёбер, произвольной степени. -/
structure Motion (F : Type*) [Field F] where
  left : List (PathSite (Polynomial F))
  near : PathSite (Polynomial F)
  middle : List (PathSite (Polynomial F))
  far : PathSite (Polynomial F)
  right : List (PathSite (Polynomial F))

namespace Motion

noncomputable abbrev D (m : Motion F) := intervalCharpoly (m.left ++ m.near :: (m.middle ++ m.far :: m.right))
noncomputable abbrev B (m : Motion F) := intervalCharpoly m.middle
noncomputable abbrev W (m : Motion F) := intervalCharpoly (m.middle ++ m.far :: m.right)
noncomputable abbrev U (m : Motion F) := intervalCharpoly m.right
noncomputable abbrev H (m : Motion F) := intervalCharpoly (m.left ++ m.near :: m.middle)
noncomputable abbrev E (m : Motion F) := intervalCharpoly m.left
noncomputable abbrev K (m : Motion F) := m.near.weight * edgeProduct m.middle
noncomputable abbrev P (m : Motion F) : Family F := C m.K * m.E

/-- Реальная матрица семейства даёт все поля касательной записи при трёх нулевых
    вариациях D,W,U. Тождество разложения, правило Лейбница и ограничения степеней —
    следствия определения характеристических многочленов. -/
noncomputable def variation (m : Motion F) (t : F)
    (hD : velocity t m.D = 0) (hW : velocity t m.W = 0) (hU : velocity t m.U = 0) :
    SpectralVariation (value t m.D) (value t m.B) (value t m.W) (value t m.U)
      (value t m.P) (value t m.E) (m.K.eval t) where
  dB := velocity t m.B
  dP := velocity t m.P
  dH := velocity t m.H
  dE := velocity t m.E
  dK := m.K.derivative.eval t
  degB := degree_velocity_lt t (Matrix.charpoly_monic _)
  degE := degree_velocity_lt t (Matrix.charpoly_monic _)
  product_rule := by rw [P, velocity_mul, velocity_C, value_C, add_comm]
  condensation := by
    have h := congrArg (velocity t) (charpoly_condensation m.left m.middle m.right m.near m.far)
    change velocity t (m.D * m.B) = velocity t (m.W * m.H - m.U * m.P) at h
    simpa only [velocity_sub, velocity_mul, hD, hW, hU, zero_mul, zero_add] using h

end Motion

noncomputable abbrev atSite (t : F) := Obstruction.mapSite (evalRingHom t)

theorem value_interval (t : F) (xs : List (PathSite F[X])) :
    value t (intervalCharpoly xs) = intervalCharpoly (xs.map (atSite t)) :=
  Obstruction.map_interval _ xs

theorem eval_edgeProduct (t : F) (xs : List (PathSite F[X])) :
    (edgeProduct xs).eval t = edgeProduct (xs.map (atSite t)) := by
  induction xs with
  | nil => simp [edgeProduct]
  | cons a xs ih =>
    change (a.weight * edgeProduct xs).eval t =
      (atSite t a).weight * edgeProduct (xs.map (atSite t))
    simp only [eval_mul, ih, PathSite.weight, atSite, Obstruction.mapSite, coe_evalRingHom]

theorem witness_edges (xs : List ℕ) : edgeProduct (xs.map Spectral.site) = 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (Spectral.site a).weight * edgeProduct (xs.map Spectral.site) = 1
    simp [Spectral.site, PathSite.weight, ih]

/-- Равенство базового значения всех диагоналей и рёбер конкретной матрице J₀. -/
structure AtWitness (m : Motion ℝ) (t : ℝ) (left middle right : List ℕ) (j k : ℕ) : Prop where
  left_eq : m.left.map (atSite t) = left.map Spectral.site
  near_eq : atSite t m.near = Spectral.site j
  middle_eq : m.middle.map (atSite t) = middle.map Spectral.site
  far_eq : atSite t m.far = Spectral.site k
  right_eq : m.right.map (atSite t) = right.map Spectral.site

theorem AtWitness.eval_K {m : Motion ℝ} {t : ℝ} {left middle right : List ℕ} {j k : ℕ}
    (h : AtWitness m t left middle right j k) : m.K.eval t = 1 := by
  have he : m.near.weight.eval t = (atSite t m.near).weight := by
    simp [PathSite.weight, atSite, Obstruction.mapSite]
  rw [Motion.K, eval_mul, he, h.near_eq, eval_edgeProduct, h.middle_eq, witness_edges]
  simp [Spectral.site, PathSite.weight]

private def distinguishes (D B W U P E : ℝ[X]) (k z : ℝ) : Prop :=
  ∀ v : SpectralVariation D B W U P E k, v.dE.eval z = 0 → v.dH.eval z = 0 →
    v.dK = 0 ∧ v.dB = 0 ∧ v.dP = 0 ∧ v.dH = 0 ∧ v.dE = 0

/-- Для перехода от спектрального J₀ к физической матрице с теми же
    диагоналями и произведениями рёбер достаточно совпадения базовых данных. -/
theorem common_root_for_equal_data (left middle right : List ℕ) (j k : ℕ)
    (hlabels : (left ++ j :: (middle ++ k :: right)).Nodup)
    (hleft : 0 < left.length) (hthreshold : left.length ≤ right.length + 2) :
    ∃ z ∈ (Spectral.block (left ++ j :: (middle ++ k :: right))).roots.toFinset,
      ∀ (m : Motion ℝ) (t : ℝ),
      value t m.D = Spectral.block (left ++ j :: (middle ++ k :: right)) →
      value t m.B = Spectral.block middle →
      value t m.W = Spectral.block (middle ++ k :: right) →
      value t m.U = Spectral.block right → value t m.E = Spectral.block left → m.K.eval t = 1 →
      velocity t m.D = 0 → velocity t m.W = 0 → velocity t m.U = 0 →
      (velocity t m.E).eval z = 0 → (velocity t m.H).eval z = 0 →
      m.K.derivative.eval t = 0 ∧ velocity t m.B = 0 ∧ velocity t m.P = 0 ∧
        velocity t m.H = 0 ∧ velocity t m.E = 0 := by
  classical
  obtain ⟨z, hz, hall⟩ := Spectral.concrete_common_spectral_root
    left middle right j k hlabels hleft hthreshold
  refine ⟨z, hz, ?_⟩
  intro m t bD bB bW bU bE bK hD hW hU hE hH
  have bP : value t m.P = Spectral.block left := by
    change Polynomial.map _ (C m.K * m.E) = _
    simp only [Polynomial.map_mul, map_C, coe_evalRingHom, bK, map_one, one_mul]
    exact bE
  have core : distinguishes (value t m.D) (value t m.B) (value t m.W) (value t m.U)
      (value t m.P) (value t m.E) (m.K.eval t) z := by
    rw [bD, bB, bW, bU, bP, bE, bK]
    exact hall
  exact core (m.variation t hD hW hU) hE hH

/-- Один корень полного конкретного характеристического многочлена работает одновременно
    для всех полиномиальных траекторий через J₀, включая все линейные вариации рёбер.
    Два последних условия — обычные производные в фиксированной спектральной точке. -/
theorem common_root_for_motions (left middle right : List ℕ) (j k : ℕ)
    (hlabels : (left ++ j :: (middle ++ k :: right)).Nodup)
    (hleft : 0 < left.length) (hthreshold : left.length ≤ right.length + 2) :
    ∃ z ∈ (Spectral.block (left ++ j :: (middle ++ k :: right))).roots.toFinset,
      ∀ (m : Motion ℝ) (t : ℝ), AtWitness m t left middle right j k →
      velocity t m.D = 0 → velocity t m.W = 0 → velocity t m.U = 0 →
      (slice z m.E).derivative.eval t = 0 → (slice z m.H).derivative.eval t = 0 →
      m.K.derivative.eval t = 0 ∧ velocity t m.B = 0 ∧ velocity t m.P = 0 ∧
        velocity t m.H = 0 ∧ velocity t m.E = 0 := by
  classical
  obtain ⟨z, hz, hall⟩ := Spectral.concrete_common_spectral_root
    left middle right j k hlabels hleft hthreshold
  refine ⟨z, hz, ?_⟩
  intro m t hw hD hW hU hE hH
  have hK := hw.eval_K
  have hP : value t m.P = Spectral.block left := by
    change Polynomial.map _ (C m.K * m.E) = _
    simp only [Polynomial.map_mul, map_C, coe_evalRingHom, hK,
      map_one, one_mul]
    change value t m.E = _
    rw [value_interval, hw.left_eq]
  change distinguishes _ _ _ _ _ _ _ z at hall
  have core : distinguishes (value t m.D) (value t m.B) (value t m.W) (value t m.U)
      (value t m.P) (value t m.E) (m.K.eval t) z := by
    rw [hP, hK]
    simpa only [Motion.D, Motion.B, Motion.W, Motion.U, Motion.E, Spectral.block,
      value_interval, List.map_append, List.map_cons, hw.left_eq, hw.near_eq,
      hw.middle_eq, hw.far_eq, hw.right_eq] using hall
  exact core (m.variation t hD hW hU)
    ((velocity_eval t z m.E).trans hE) ((velocity_eval t z m.H).trans hH)

theorem slice_interval (z : F) (xs : List (PathSite F[X])) :
    slice z (intervalCharpoly xs) = cont (xs.map (shiftedSite (C z))) := by
  rw [slice, intervalCharpoly, charpoly_eq_cont]
  suffices h : (((run (xs.map pencilSite) (1,0)).1).eval (C z),
      ((run (xs.map pencilSite) (1,0)).2).eval (C z)) =
      run (xs.map (shiftedSite (C z))) (1,0) from congrArg Prod.fst h
  induction xs with
  | nil => simp [run]
  | cons a xs ih =>
    have ha := congrArg Prod.fst ih
    have hb := congrArg Prod.snd ih
    simp only [Prod.fst, Prod.snd] at ha hb
    simp [run, step, pencilSite, shiftedSite, PathSite.weight, ha, hb]

private theorem map_entry {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (xs : List (PathSite R)) (i j : ℕ) : φ (entry xs i j) =
      entry (xs.map (Obstruction.mapSite φ)) i j := by
  induction xs generalizing i j with
  | nil => simp [entry]
  | cons a xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => by_cases h : j = 0 <;> simp [entry, h, Obstruction.mapSite]
    | succ i =>
      cases j with
      | zero => by_cases h : i = 0 <;> simp [entry, h, Obstruction.mapSite]
      | succ j => exact ih i j

private theorem symmetric_path {R : Type*} [CommRing R] (xs : List (PathSite R))
    (h : ∀ a ∈ xs, a.upper = a.lower) : (pathMatrix xs).transpose = pathMatrix xs := by
  have hm : xs.map swapSite = xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      have ha := h a List.mem_cons_self
      have he : swapSite a = a := by cases a; simp_all [swapSite]
      simp [he, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
  funext i j
  exact (entry_swap xs i.val j.val).symm.trans
    (congrArg (fun ys : List (PathSite R) => entry ys i.val j.val) hm)

/-- Измеряемая по левой границе величина в спектральной калибровке:
    произведение рёбер до отмеченной вершины и отношение двух кофакторов одного столбца. -/
noncomputable def cofactorGain (z : ℝ) (pre : List (PathSite ℝ[X])) (v : PathSite ℝ[X])
    (post : List (PathSite ℝ[X])) (ell : Fin (pre ++ v :: post).length) (u : ℝ) : ℝ :=
  let ps := pre.map (shiftedSite (C z))
  let ss := ps ++ shiftedSite (C z) v :: post.map (shiftedSite (C z))
  let e : Fin ss.length := ⟨0, by simp [ss]⟩
  let i : Fin ss.length := ⟨ps.length, by simp [ss]⟩
  let ℓ : Fin ss.length := ⟨ell.val, by simpa [ss, ps] using ell.isLt⟩
  let A := (pathMatrix ss).adjugate
  (directedProduct ps * A i ℓ).eval u / (A e ℓ).eval u

/-- На J₀ инфинитезимальное изменение фактического отношения кофакторов есть
    оценка вариации ведущего характеристического многочлена. Предполагается
    симметричная полиномиальная траектория и δD=0, а положение утечки произвольно. -/
theorem cofactorGain_hasDerivAt (z t : ℝ) (pre : List (PathSite ℝ[X])) (v : PathSite ℝ[X])
    (post : List (PathSite ℝ[X])) (ell : Fin (pre ++ v :: post).length)
    (a : ℕ) (labels : List ℕ) (hd : (a :: labels).Nodup)
    (hz : (Spectral.block (a :: labels)).eval z = 0)
    (hbase : (pre ++ v :: post).map (atSite t) = (a :: labels).map Spectral.site)
    (hsym : ∀ w ∈ pre ++ v :: post, w.upper = w.lower)
    (hD : velocity t (intervalCharpoly (pre ++ v :: post)) = 0) :
    HasDerivAt (cofactorGain z pre v post ell) ((velocity t (intervalCharpoly pre)).eval z) t := by
  let f : PathSite ℝ[X] → PathSite ℝ[X] := shiftedSite (C z)
  let ys := pre.map f ++ f v :: post.map f
  have hsplit : ys = (pre ++ v :: post).map f := by simp [ys]
  have hcomm : atSite t ∘ f = shiftedSite z ∘ atSite t := by
    funext w
    simp [Function.comp_def, atSite, Obstruction.mapSite, f, shiftedSite]
  have hsite : shiftedSite z ∘ Spectral.site = Spectral.shiftedSite z := by
    funext i
    simp [Function.comp_def, shiftedSite, Spectral.site, Spectral.shiftedSite]
  have he : ys.map (atSite t) = (a :: labels).map (Spectral.shiftedSite z) := by
    rw [hsplit, List.map_map, hcomm, ← List.map_map, hbase, List.map_map, hsite]
  let eqv : Fin ys.length ≃ Fin ((a :: labels).map (Spectral.shiftedSite z)).length :=
    finCongr (by simpa only [List.length_map] using congrArg List.length he)
  have hM : (evalRingHom t).mapMatrix (pathMatrix ys) =
      (pathMatrix ((a :: labels).map (Spectral.shiftedSite z))).submatrix eqv eqv := by
    ext i j
    change (evalRingHom t) (entry ys i.val j.val) =
      entry ((a :: labels).map (Spectral.shiftedSite z)) i.val j.val
    rw [map_entry, ← he]
  have hS : (pathMatrix ys).transpose = pathMatrix ys := by
    apply symmetric_path
    intro w hw
    rw [hsplit] at hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
    exact congrArg Neg.neg (hsym b hb)
  have hdet : (pathMatrix ys).det.derivative.eval t = 0 := by
    rw [det_eq_cont, hsplit, ← slice_interval, ← velocity_eval, hD, eval_zero]
  let ℓ : Fin ys.length := ⟨ell.val, by simpa [ys] using ell.isLt⟩
  have hh := SpectralGain.witness_gain_hasDerivAt (pre.map f) (post.map f) (f v) ℓ
    t z a labels hd hz eqv rfl hS hM hdet
  rw [velocity_eval, slice_interval]
  exact hh

/-- Один и тот же номер утечки в разрезах у первого и у второго выходов. -/
def Motion.farLeak (m : Motion F)
    (ell : Fin (m.left ++ m.near :: (m.middle ++ m.far :: m.right)).length) :
    Fin ((m.left ++ m.near :: m.middle) ++ m.far :: m.right).length :=
  ⟨ell.val, by simpa only [List.append_assoc, List.cons_append] using ell.isLt⟩

/-- Общая точка λ различает все полиномиальные касательные через J₀ двумя
    измеряемыми отношениями кофакторов, для любого положения одного и того же
    столбца утечки. Условия δD=δW=δU=0 оставлены в явном виде. -/
theorem common_root_for_gains (left middle right : List ℕ) (j k : ℕ)
    (hlabels : (left ++ j :: (middle ++ k :: right)).Nodup)
    (hleft : 0 < left.length) (hthreshold : left.length ≤ right.length + 2) :
    ∃ z ∈ (Spectral.block (left ++ j :: (middle ++ k :: right))).roots.toFinset,
      ∀ (m : Motion ℝ) (t : ℝ), AtWitness m t left middle right j k →
      (∀ w ∈ m.left ++ m.near :: (m.middle ++ m.far :: m.right), w.upper = w.lower) →
      velocity t m.D = 0 → velocity t m.W = 0 → velocity t m.U = 0 →
      ∀ ell : Fin (m.left ++ m.near :: (m.middle ++ m.far :: m.right)).length,
      deriv (cofactorGain z m.left m.near (m.middle ++ m.far :: m.right) ell) t = 0 →
      deriv (cofactorGain z (m.left ++ m.near :: m.middle) m.far m.right (m.farLeak ell)) t = 0 →
      m.K.derivative.eval t = 0 ∧ velocity t m.B = 0 ∧ velocity t m.P = 0 ∧
        velocity t m.H = 0 ∧ velocity t m.E = 0 := by
  classical
  cases left with
  | nil => simp at hleft
  | cons a left =>
    obtain ⟨z, hz, hall⟩ := common_root_for_motions
      (a :: left) middle right j k hlabels hleft hthreshold
    refine ⟨z, hz, ?_⟩
    intro m t hw hsym hD hW hU ell hj hk
    let tailLabels := left ++ j :: (middle ++ k :: right)
    have hroot : (Spectral.block (a :: tailLabels)).eval z = 0 :=
      isRoot_of_mem_roots (Multiset.mem_toFinset.mp hz)
    have hbase : (m.left ++ m.near :: (m.middle ++ m.far :: m.right)).map (atSite t) =
        (a :: tailLabels).map Spectral.site := by
      simp only [List.map_append, List.map_cons, hw.left_eq, hw.near_eq, hw.middle_eq,
        hw.far_eq, hw.right_eq, tailLabels]
      rfl
    have hnear := cofactorGain_hasDerivAt z t m.left m.near (m.middle ++ m.far :: m.right)
      ell a tailLabels hlabels hroot hbase hsym hD
    have hfar := cofactorGain_hasDerivAt z t (m.left ++ m.near :: m.middle) m.far m.right
      (m.farLeak ell) a tailLabels hlabels hroot
      (by simpa only [List.append_assoc, List.cons_append] using hbase)
      (by simpa only [List.append_assoc, List.cons_append] using hsym)
      (by simpa only [List.append_assoc, List.cons_append] using hD)
    exact hall m t hw hD hW hU
      ((velocity_eval t z m.E).symm.trans (hnear.deriv.symm.trans hj))
      ((velocity_eval t z m.H).symm.trans (hfar.deriv.symm.trans hk))

/-- Рациональная матрица наблюдений с общим знаменателем q. Колонки могут быть
    координатами базиса любого фиксированного пространства касательных направлений. -/
noncomputable def rationalMatrix {r n : ℕ} (N : Matrix (Fin r) (Fin n) ℝ[X]) (q : ℝ[X])
    (z : ℝ) : Matrix (Fin r) (Fin n) ℝ := (q.eval z)⁻¹ • N.map (Polynomial.eval z)

private theorem gram_injective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℝ) :
    (A.transpose * A).det ≠ 0 ↔ Function.Injective A.mulVec := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.mulVec_injective_iff_isUnit, ← Matrix.coe_mulVecLin, ← LinearMap.ker_eq_bot,
    Matrix.ker_mulVecLin_transpose_mul_self, LinearMap.ker_eq_bot, Matrix.coe_mulVecLin]

private theorem det_gram_eval {r n : ℕ} (N : Matrix (Fin r) (Fin n) ℝ[X]) (z : ℝ) :
    (N.transpose * N).det.eval z =
      ((N.map (Polynomial.eval z)).transpose * N.map (Polynomial.eval z)).det := by
  change evalRingHom z (N.transpose * N).det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
  rfl

/-- Инъективность всей рациональной матрицы в одной точке продолжается на
    сколь угодно большой сдвиг, одновременно для всех касательных направлений.
    Размеры могут быть нулевыми. Ненулевость одного многочлена удостоверяет
    определитель матрицы Грама числителя. -/
theorem rational_injectivity_above {r n : ℕ} (N : Matrix (Fin r) (Fin n) ℝ[X]) (q : ℝ[X])
    (z₀ bound : ℝ) (hq : q.eval z₀ ≠ 0)
    (hinj : Function.Injective (rationalMatrix N q z₀).mulVec) :
    ∃ z, bound < z ∧ q.eval z ≠ 0 ∧ Function.Injective (rationalMatrix N q z).mulVec := by
  let G := (N.transpose * N).det
  have base : Function.Injective (N.map (Polynomial.eval z₀)).mulVec := by
    intro x y h
    apply hinj
    simp only [rationalMatrix, Matrix.smul_mulVec_assoc, h]
  have hG : G.eval z₀ ≠ 0 := (det_gram_eval N z₀).trans_ne ((gram_injective _).2 base)
  obtain ⟨z, hz, hqz, hratio⟩ := rational_minor_above G q z₀ bound (div_ne_zero hG hq)
  have hGz : G.eval z ≠ 0 := (div_ne_zero_iff.mp hratio).1
  have hN := (gram_injective _).1 ((det_gram_eval N z).symm.trans_ne hGz)
  refine ⟨z, hz, hqz, ?_⟩
  intro x y h
  apply hN
  apply smul_right_injective (Fin r → ℝ) (inv_ne_zero hqz)
  simpa only [rationalMatrix, Matrix.smul_mulVec_assoc] using h

section Jets

/-- Подстановка t+ε в многочлен: значение и фактическая производная, ε²=0. -/
noncomputable def jet (t : F) : F[X] →+* DualNumber F where
  toFun p := (p.eval t, p.derivative.eval t)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' p q := by apply TrivSqZeroExt.ext <;> simp
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [derivative_mul, mul_comm, add_comm]

noncomputable def stationary (t : F) : F[X] →+* DualNumber F :=
  (TrivSqZeroExt.inlHom F F).comp (evalRingHom t)

theorem jet_eq_stationary {t : F} {p : F[X]} :
    jet t p = stationary t p ↔ p.derivative.eval t = 0 :=
  ⟨fun h => congrArg TrivSqZeroExt.snd h, fun h => TrivSqZeroExt.ext rfl h⟩

theorem map_jet_eq_stationary {t : F} {p : Family F} :
    p.map (jet t) = p.map (stationary t) ↔ velocity t p = 0 := by
  constructor
  · intro h
    ext n
    simpa only [coeff_velocity, coeff_zero] using jet_eq_stationary.mp
      (show jet t (p.coeff n) = stationary t (p.coeff n) by
        simpa only [coeff_map] using congrArg (fun q : (DualNumber F)[X] => q.coeff n) h)
  · intro h
    apply Polynomial.ext
    intro n
    rw [coeff_map, coeff_map]
    apply jet_eq_stationary.mpr
    simpa only [coeff_velocity, coeff_zero] using congrArg (fun q : F[X] => q.coeff n) h

theorem residue_jet (t : F) (p : Family F) :
    (p.map (jet t)).map ThreeBlocks.residue = value t p := by
  ext n
  simp only [coeff_map, coeff_value]
  rfl

end Jets

section Encoding

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem chi_empty : intervalCharpoly ([] : List (PathSite S)) = 1 :=
  (charpoly_eq_cont _).trans cont_nil

private theorem chi_one (u : PathSite S) : intervalCharpoly [u] = X - C u.diag :=
  (charpoly_eq_cont _).trans (cont_singleton _)

private theorem chi_step (a b : PathSite S) (xs : List (PathSite S)) :
    intervalCharpoly (a :: b :: xs) = (X - C a.diag) * intervalCharpoly (b :: xs) -
      C a.weight * intervalCharpoly xs := by
  simp only [intervalCharpoly, charpoly_eq_cont, List.map_cons, cont_cons_cons, pencil_weight]
  rfl

/-- У определителя и его хвоста существенны все диагонали и ровно n−1 весов. -/
private theorem interval_pair_congr (xs ys : List (PathSite S))
    (hd : xs.map PathSite.diag = ys.map PathSite.diag)
    (hw : xs.dropLast.map PathSite.weight = ys.dropLast.map PathSite.weight) :
    intervalCharpoly xs = intervalCharpoly ys ∧
      intervalCharpoly xs.tail = intervalCharpoly ys.tail := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact ⟨rfl, rfl⟩
    | cons => simp at hd
  | cons a xs ih =>
    cases ys with
    | nil => simp at hd
    | cons b ys =>
      obtain ⟨hab, htail⟩ := List.cons.inj hd
      cases xs with
      | nil =>
        cases ys with
        | nil => exact ⟨by rw [chi_one, chi_one, hab], rfl⟩
        | cons => simp at htail
      | cons c xs =>
        cases ys with
        | nil => simp at htail
        | cons d ys =>
          simp only [List.dropLast_cons₂, List.map_cons, List.cons.injEq] at hw
          obtain ⟨h₁, h₂⟩ := ih (d :: ys) htail hw.2
          refine ⟨?_, h₁⟩
          rw [chi_step, chi_step, hab, hw.1, h₁]
          exact congrArg (fun v => (X - C b.diag) * intervalCharpoly (d :: ys) - C b.weight * v) h₂

private structure Represents (φ : R →+* S) (ys : List (PathSite S)) (xs : List (PathSite R)) : Prop where
  diagonals : ys.map PathSite.diag = xs.map (fun a => φ a.diag)
  weights : ys.dropLast.map PathSite.weight = xs.dropLast.map (fun a => φ a.weight)

private theorem Represents.interval {φ : R →+* S} {ys : List (PathSite S)} {xs : List (PathSite R)}
    (h : Represents φ ys xs) : intervalCharpoly ys = (intervalCharpoly xs).map φ := by
  rw [Obstruction.map_interval]
  apply (interval_pair_congr _ _ ?_ ?_).1
  · simpa only [List.map_map, Function.comp_def, Obstruction.mapSite] using h.diagonals
  · simpa [← List.map_dropLast, List.map_map, Function.comp_def, Obstruction.mapSite,
      PathSite.weight] using h.weights

private def normSite (φ : R →+* S) (a : PathSite R) : PathSite S := ⟨φ a.diag, φ a.weight, 1⟩

private theorem represents_norm (φ : R →+* S) (xs : List (PathSite R)) :
    Represents φ (xs.map (normSite φ)) xs := by
  constructor <;> simp [← List.map_dropLast, Function.comp_def, normSite, PathSite.weight]

private theorem Represents.add_head {φ : R →+* S} {ys : List (PathSite S)} {xs : List (PathSite R)}
    (h : Represents φ ys xs) {a : PathSite S} {b : PathSite R} (hd : a.diag = φ b.diag)
    (hw : a.weight = φ b.weight) : Represents φ (a :: ys) (b :: xs) := by
  refine ⟨by simp only [List.map_cons, hd, h.diagonals], ?_⟩
  have hn : ys.length = xs.length := by simpa using congrArg List.length h.diagonals
  cases xs with
  | nil => cases ys <;> simp_all
  | cons b xs =>
    cases ys with
    | nil => simp at hn
    | cons a ys =>
      simpa only [List.dropLast_cons₂, List.map_cons, hw] using
        (congrArg (List.cons (φ _)) h.weights)

private theorem Represents.prefix {φ : R →+* S} {ys : List (PathSite S)} {xs : List (PathSite R)}
    (h : Represents φ ys xs) (pre : List (PathSite R)) :
    Represents φ (pre.map (normSite φ) ++ ys) (pre ++ xs) := by
  induction pre with
  | nil => exact h
  | cons a pre ih =>
    apply ih.add_head rfl
    simp [normSite, PathSite.weight]

/-- Реальные веса обратимы после взятия первой струи, когда их исходное
    значение ненулевое. В поле многочленов обращать движущийся вес не требуется. -/
private noncomputable def backPack (φ : R →+* S) :
    (rev : List (PathSite R)) → (v : PathSite R) → (∀ a ∈ rev, IsUnit (φ a.weight)) →
    JacobiData S rev.length
  | [], v, _ => .single (φ v.diag)
  | a :: xs, v, h => .extend (φ v.diag) (h a List.mem_cons_self).unit
      (backPack φ xs a (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem back_diag (φ : R →+* S) (rev : List (PathSite R)) (v : PathSite R) (h) :
    ThreeBlocks.lastDiagonal (backPack φ rev v h) = φ v.diag := by cases rev <;> rfl

private theorem back_before (φ : R →+* S) (rev : List (PathSite R)) (v : PathSite R) (h) :
    ThreeBlocks.before (backPack φ rev v h) = rev.reverse.map (normSite φ) := by
  induction rev generalizing v with
  | nil => rfl
  | cons a xs ih =>
    simp only [backPack, ThreeBlocks.before, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, ThreeBlocks.lastSite, back_diag, IsUnit.unit_spec, ih, normSite]

private noncomputable def frontPack (φ : R →+* S) (v : PathSite R) :
    (xs : List (PathSite R)) → (∀ a ∈ (v :: xs).dropLast, IsUnit (φ a.weight)) →
    JacobiData S xs.length
  | [], _ => .single (φ v.diag)
  | a :: xs, h => .extend (φ v.diag) (h v (by simp)).unit
      (frontPack φ a xs (fun b hb => h b (by simp only [List.dropLast_cons₂]; exact List.mem_cons_of_mem _ hb)))

private theorem front_rep (φ : R →+* S) (v : PathSite R) (xs : List (PathSite R)) (h) :
    Represents φ (frontPack φ v xs h).sites (v :: xs) := by
  induction xs generalizing v with
  | nil => exact ⟨rfl, rfl⟩
  | cons a xs ih =>
    apply (ih a _).add_head rfl
    simp [PathSite.weight, IsUnit.unit_spec]

private noncomputable def tailPack (φ : R →+* S) (v : PathSite R) :
    (xs : List (PathSite R)) → (∀ a ∈ (v :: xs).dropLast, IsUnit (φ a.weight)) →
    ThreeBlocks.Tail S xs.length
  | [], _ => .empty
  | a :: xs, h => .nonempty (h v (by simp)).unit
      (frontPack φ a xs (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem tail_rep (φ : R →+* S) (v : PathSite R) (xs : List (PathSite R)) (h) :
    Represents φ (tailPack φ v xs h).sites xs := by
  cases xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons a xs => apply front_rep

/-- Разбиение настоящих рёбер. Ребро после последней вершины отсутствует даже в
    сингулярном случае пустого хвоста. -/
private structure WeightUnits (φ : F[X] →+* S) (m : Motion F) : Prop where
  left : ∀ a ∈ m.left, IsUnit (φ a.weight)
  near : IsUnit (φ m.near.weight)
  middle : ∀ a ∈ m.middle, IsUnit (φ a.weight)
  tail_ : ∀ a ∈ (m.far :: m.right).dropLast, IsUnit (φ a.weight)

private noncomputable def pack (φ : F[X] →+* S) (m : Motion F) (h : WeightUnits φ m) :
    ThreeBlocks.Blocks S m.left.reverse.length m.middle.reverse.length m.right.length where
  left := backPack φ m.left.reverse m.near (fun a ha => h.left a (List.mem_reverse.mp ha))
  bridge := h.near.unit
  middle := backPack φ m.middle.reverse m.far (fun a ha => h.middle a (List.mem_reverse.mp ha))
  tail_ := tailPack φ m.far m.right h.tail_

private theorem pack_reps (φ : F[X] →+* S) (m : Motion F) (h : WeightUnits φ m) :
    let x := pack φ m h
    Represents φ x.full (m.left ++ m.near :: (m.middle ++ m.far :: m.right)) ∧
    Represents φ (ThreeBlocks.rightPart x.middle x.tail_) (m.middle ++ m.far :: m.right) ∧
    Represents φ x.tail_.sites m.right ∧
    Represents φ (ThreeBlocks.before x.middle) m.middle ∧
    Represents φ (ThreeBlocks.before x.left) m.left := by
  intro x
  have hL : ThreeBlocks.before x.left = m.left.map (normSite φ) := by
    simp only [x, pack, back_before, List.reverse_reverse]
  have hM : ThreeBlocks.before x.middle = m.middle.map (normSite φ) := by
    simp only [x, pack, back_before, List.reverse_reverse]
  have hT : Represents φ x.tail_.sites m.right := tail_rep φ m.far m.right h.tail_
  have hF : Represents φ (ThreeBlocks.lastSite x.middle x.tail_.entrance :: x.tail_.sites)
      (m.far :: m.right) := by
    have hd : (ThreeBlocks.lastSite x.middle x.tail_.entrance).diag = φ m.far.diag := back_diag _ _ _ _
    by_cases he : m.right = []
    ·
      have htm : x.tail_.sites = [] := by
        have hh := congrArg List.length hT.diagonals
        simpa [he] using hh
      constructor
      · simp only [List.map_cons, hd, hT.diagonals]
      · simp only [htm, List.dropLast, List.map_nil]
        simp [he]
    · apply hT.add_head hd
      have entrance (ys : List (PathSite F[X])) (hy : ys ≠ [])
          (hu : ∀ b ∈ (m.far :: ys).dropLast, IsUnit (φ b.weight)) :
          (tailPack φ m.far ys hu).entrance = φ m.far.weight := by
        cases ys with
        | nil => contradiction
        | cons => simp [tailPack, ThreeBlocks.Tail.entrance, IsUnit.unit_spec]
      change (tailPack φ m.far m.right h.tail_).entrance * 1 = _
      exact (mul_one _).trans (entrance _ he _)
  have hW : Represents φ (ThreeBlocks.rightPart x.middle x.tail_) (m.middle ++ m.far :: m.right) := by
    rw [ThreeBlocks.rightPart, hM]
    exact hF.prefix m.middle
  have hD : Represents φ x.full (m.left ++ m.near :: (m.middle ++ m.far :: m.right)) := by
    rw [ThreeBlocks.Blocks.full, hL]
    apply Represents.prefix
    apply hW.add_head (back_diag _ _ _ _)
    change (h.near.unit : S) * 1 = φ m.near.weight
    rw [mul_one, IsUnit.unit_spec]
  exact ⟨hD, hW, hT, hM ▸ represents_norm φ _, hL ▸ represents_norm φ _⟩

private theorem edge_norm (φ : R →+* S) (xs : List (PathSite R)) :
    edgeProduct (xs.map (normSite φ)) = φ (edgeProduct xs) := by
  induction xs with
  | nil => simp [edgeProduct]
  | cons a xs ih =>
    change (φ a.weight * 1) * edgeProduct (xs.map (normSite φ)) = φ (a.weight * edgeProduct xs)
    rw [mul_one, ih, map_mul]

private theorem pack_data (φ : F[X] →+* S) (m : Motion F) (h : WeightUnits φ m) :
    ThreeBlocks.data (pack φ m h) =
      ⟨m.D.map φ, m.W.map φ, m.U.map φ, m.B.map φ, m.P.map φ⟩ := by
  obtain ⟨hD, hW, hU, hB, hE⟩ := pack_reps φ m h
  have hK : ((pack φ m h).K : S) = φ m.K := by
    change (h.near.unit : S) * (ThreeBlocks.internalWeights (pack φ m h).middle : S) = _
    rw [IsUnit.unit_spec, ← ThreeBlocks.edgeProduct_before]
    simp only [pack, back_before, List.reverse_reverse, edge_norm, Motion.K, map_mul]
  have hP : (pack φ m h).P = m.P.map φ := by
    rw [ThreeBlocks.Blocks.P, Motion.P, Polynomial.map_mul, map_C, hK, hE.interval]
  exact congrArg₂ (fun p q => ThreeBlocks.Five.mk p q _ _ _)
    hD.interval hW.interval |>.trans (by rw [← hU.interval, ← hB.interval, ← hP]; rfl)

end Encoding

abbrev Motion.sites (m : Motion F) := m.left ++ m.near :: (m.middle ++ m.far :: m.right)

private theorem Motion.edges (m : Motion F) : m.sites.dropLast =
    m.left ++ m.near :: (m.middle ++ (m.far :: m.right).dropLast) := by
  rw [Motion.sites, List.dropLast_append_of_ne_nil (by simp),
    List.dropLast_cons_of_ne_nil (by simp), List.dropLast_append_of_ne_nil (by simp)]

private theorem units_of_regular {S : Type*} [CommRing S] (t : F) (φ : F[X] →+* S)
    (hφ : ∀ p : F[X], p.eval t ≠ 0 → IsUnit (φ p)) (m : Motion F)
    (h : ∀ a ∈ m.sites.dropLast, a.weight.eval t ≠ 0) : WeightUnits φ m := by
  rw [m.edges] at h
  refine ⟨fun a ha => hφ _ (h a (by simp [ha])), hφ _ (h _ (by simp)),
    fun a ha => hφ _ (h a (by simp [ha])), fun a ha => hφ _ (h a (by simp [ha]))⟩

/-- Касательная жёсткость настоящей полиномиальной матрицы: если пять
    матричных полиномов неподвижны, каждая диагональ и произведение двух
    направленных скоростей каждого настоящего ребра имеют нулевую производную.
    Достаточны ненулевые базовые веса и взаимная простота B,U при t. -/
theorem motion_tangent_rigidity (m : Motion F) (t : F)
    (hreg : ∀ a ∈ m.sites.dropLast, a.weight.eval t ≠ 0)
    (hc : IsCoprime (value t m.B) (value t m.U))
    (hD : velocity t m.D = 0) (hW : velocity t m.W = 0) (hU : velocity t m.U = 0)
    (hB : velocity t m.B = 0) (hP : velocity t m.P = 0) :
    (∀ a ∈ m.sites, a.diag.derivative.eval t = 0) ∧
    (∀ a ∈ m.sites.dropLast, a.weight.derivative.eval t = 0) := by
  let xj := jet t
  let x₀ := stationary t
  have hj : WeightUnits xj m := units_of_regular t xj (fun p hp =>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hp)) m hreg
  have h₀ : WeightUnits x₀ m := units_of_regular t x₀ (fun p hp =>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hp)) m hreg
  let x := pack xj m hj
  let y := pack x₀ m h₀
  have hx : ThreeBlocks.data x =
      ⟨m.D.map xj, m.W.map xj, m.U.map xj, m.B.map xj, m.P.map xj⟩ := pack_data _ _ _
  have hy : ThreeBlocks.data y =
      ⟨m.D.map x₀, m.W.map x₀, m.U.map x₀, m.B.map x₀, m.P.map x₀⟩ := pack_data _ _ _
  have hxy : x = y := by
    apply ThreeBlocks.recover_first_variations
    · rw [hx]
      simpa only [xj, residue_jet] using hc
    · rw [hx, hy,
        show m.D.map xj = m.D.map x₀ from map_jet_eq_stationary.mpr hD,
        show m.W.map xj = m.W.map x₀ from map_jet_eq_stationary.mpr hW,
        show m.U.map xj = m.U.map x₀ from map_jet_eq_stationary.mpr hU,
        show m.B.map xj = m.B.map x₀ from map_jet_eq_stationary.mpr hB,
        show m.P.map xj = m.P.map x₀ from map_jet_eq_stationary.mpr hP]
  have rj := (pack_reps xj m hj).1
  have r₀ := (pack_reps x₀ m h₀).1
  have hfull : x.full = y.full := congrArg ThreeBlocks.Blocks.full hxy
  have hd := rj.diagonals.symm.trans ((congrArg (List.map PathSite.diag) hfull).trans r₀.diagonals)
  have hw := rj.weights.symm.trans
    ((congrArg (fun l : List (PathSite (DualNumber F)) => l.dropLast.map PathSite.weight) hfull).trans r₀.weights)
  exact ⟨fun a ha => jet_eq_stationary.mp (List.map_inj_left.mp hd a ha),
    fun a ha => jet_eq_stationary.mp (List.map_inj_left.mp hw a ha)⟩

/-- Концевой вход. Один λ работает одновременно для всех полиномиальных
    траекторий настоящих диагоналей и рёбер с указанными исходными
    характеристическими полиномами. Никакой гипотезы о реконструкции
    касательных или взаимной простоте здесь нет. -/
theorem common_root_recovers_entries (left middle right : List ℕ) (j k : ℕ)
    (hlabels : (left ++ j :: (middle ++ k :: right)).Nodup)
    (hleft : 0 < left.length) (hthreshold : left.length ≤ right.length + 2) :
    ∃ z ∈ (Spectral.block (left ++ j :: (middle ++ k :: right))).roots.toFinset,
      ∀ (m : Motion ℝ) (t : ℝ),
      (∀ a ∈ m.sites.dropLast, a.weight.eval t ≠ 0) →
      value t m.D = Spectral.block (left ++ j :: (middle ++ k :: right)) →
      value t m.B = Spectral.block middle →
      value t m.W = Spectral.block (middle ++ k :: right) →
      value t m.U = Spectral.block right → value t m.E = Spectral.block left → m.K.eval t = 1 →
      velocity t m.D = 0 → velocity t m.W = 0 → velocity t m.U = 0 →
      (velocity t m.E).eval z = 0 → (velocity t m.H).eval z = 0 →
      (∀ a ∈ m.sites, a.diag.derivative.eval t = 0) ∧
      (∀ a ∈ m.sites.dropLast, a.weight.derivative.eval t = 0) := by
  classical
  obtain ⟨z, hz, hall⟩ := common_root_for_equal_data left middle right j k hlabels hleft hthreshold
  refine ⟨z, hz, ?_⟩
  intro m t hreg bD bB bW bU bE bK hD hW hU hE hH
  have h := hall m t bD bB bW bU bE bK hD hW hU hE hH
  have hn := List.nodup_append.mp (List.nodup_cons.mp (List.nodup_append.mp hlabels).2.1).2
  have hc : IsCoprime (value t m.B) (value t m.U) := by
    rw [bB, bU]
    exact Spectral.separated_coprime hn.1 (fun a ha hb => hn.2.2 ha (List.mem_cons_of_mem _ hb))
  exact motion_tangent_rigidity m t hreg hc hD hW hU h.2.1 h.2.2.1

end Catenary.WitnessVariation
