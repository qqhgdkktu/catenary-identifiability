import Chain.PolynomialChain
import Chain.ResolventGeneral
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! # Спектральная точка с единичными рёбрами и разделёнными диагоналями -/

namespace Catenary.Spectral

open Polynomial Continuant

/-- Вершина с меткой t имеет диагональ −10t и оба соседних коэффициента 1. -/
def site (t : ℕ) : PathSite ℝ := ⟨-(10 * (t : ℝ)), 1, 1⟩

noncomputable abbrev block (xs : List ℕ) : ℝ[X] := intervalCharpoly (xs.map site)

@[simp] theorem block_nil : block [] = 1 :=
  (charpoly_eq_cont ([] : List (PathSite ℝ))).trans cont_nil

@[simp] theorem block_one (t : ℕ) : block [t] = X - C (site t).diag :=
  (charpoly_eq_cont [site t]).trans (cont_singleton _)

theorem block_step (t u : ℕ) (xs : List ℕ) :
    block (t :: u :: xs) = (X - C (site t).diag) * block (u :: xs) - block xs := by
  simp only [block, intervalCharpoly, charpoly_eq_cont, List.map_cons, cont_cons_cons,
    pencil_weight, site, PathSite.weight, one_mul, map_one]
  simp [pencilSite]

def diagProduct (z : ℝ) (xs : List ℕ) : ℝ :=
  (xs.map (fun t : ℕ => z + 10 * (t : ℝ))).prod

private theorem pivot_dominates (a q r : ℝ) (ha : 2 ≤ |a|) (h : |r| < |q|) :
    |q| < |a * q - r| ∧ 0 < (a * q - r) * (a * q) := by
  have hq : 0 < |q| := (abs_nonneg _).trans_lt h
  have hprod : 2 * |q| ≤ |a * q| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ha hq.le
  have htriangle : |a * q| ≤ |a * q - r| + |r| := by
    calc
      _ = |(a * q - r) + r| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add_le _ _
  refine ⟨by linarith, ?_⟩
  rcases lt_or_ge 0 (a * q) with hp | hp
  · rw [abs_of_pos hp] at hprod
    exact mul_pos (by linarith [le_abs_self r]) hp
  · rw [abs_of_nonpos hp] at hprod
    exact mul_pos_of_neg_of_neg (by linarith [neg_le_abs r]) (by linarith)

/-- Вне интервалов радиуса 2 знак определителя совпадает со знаком
    произведения диагональных элементов, и следующий определитель меньше по модулю. -/
theorem dominant_block (xs : List ℕ) (z : ℝ) (hf : ∀ t ∈ xs, 2 ≤ |z + 10 * (t : ℝ)|) :
    0 < (block xs).eval z * diagProduct z xs ∧
      (xs ≠ [] → |(block xs.tail).eval z| < |(block xs).eval z|) := by
  induction xs with
  | nil => simp [diagProduct]
  | cons t xs ih =>
    have ht := hf t (by simp)
    have htail := ih (fun u hu => hf u (by simp [hu]))
    cases xs with
    | nil =>
      simp only [block_one, block_nil, List.tail_cons, eval_sub, eval_X, eval_C, site,
        sub_neg_eq_add, diagProduct, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, eval_one, abs_one]
      have hne : z + 10 * (t : ℝ) ≠ 0 := by
        intro h
        rw [h, abs_zero] at ht
        linarith
      exact ⟨mul_self_pos.mpr hne, fun _ => by linarith⟩
    | cons u rest =>
      have hr := htail.2 (by simp)
      have hstep := pivot_dominates (z + 10 * (t : ℝ)) ((block (u :: rest)).eval z)
        ((block rest).eval z) ht hr
      have heval : (block (t :: u :: rest)).eval z =
          (z + 10 * (t : ℝ)) * (block (u :: rest)).eval z - (block rest).eval z := by
        rw [block_step]
        simp [site]
      rw [heval]
      constructor
      · change 0 < _ * ((z + 10 * (t : ℝ)) * diagProduct z (u :: rest))
        apply pos_of_mul_pos_left (b := ((block (u :: rest)).eval z) ^ 2) _ (sq_nonneg _)
        convert mul_pos hstep.2 htail.1 using 1
        ring
      · exact fun _ => hstep.1

theorem real_root_near_label {xs : List ℕ} {z : ℝ} (hz : (block xs).eval z = 0) :
    ∃ t ∈ xs, |z + 10 * (t : ℝ)| < 2 := by
  by_contra! h
  have hpos := (dominant_block xs z h).1
  simp [hz] at hpos

private theorem different_centres {t u : ℕ} {z : ℝ} (ht : |z + 10 * (t : ℝ)| ≤ 3)
    (hu : |z + 10 * (u : ℝ)| ≤ 3) : t = u := by
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  obtain ⟨hul, hur⟩ := abs_le.mp hu
  rcases lt_trichotomy t u with h | h | h
  · have hn : (t : ℝ) + 1 ≤ u := by exact_mod_cast h
    linarith
  · exact h
  · have hn : (u : ℝ) + 1 ≤ t := by exact_mod_cast h
    linarith

/-- Непересекающиеся множества меток дают блоки без общих вещественных корней. -/
theorem separated_real_roots {xs ys : List ℕ} (hxy : xs.Disjoint ys) {z : ℝ}
    (hx : (block xs).eval z = 0) : (block ys).eval z ≠ 0 := by
  intro hy
  obtain ⟨t, ht, hzt⟩ := real_root_near_label hx
  obtain ⟨u, hu, hzu⟩ := real_root_near_label hy
  have h := different_centres (le_trans hzt.le (by norm_num)) (le_trans hzu.le (by norm_num))
  exact hxy ht (h ▸ hu)

private def lo (t : ℕ) : ℝ := -10 * (t : ℝ) - 3
private def hi (t : ℕ) : ℝ := -10 * (t : ℝ) + 3

private theorem end_bounds (t u : ℕ) :
    2 ≤ |lo t + 10 * (u : ℝ)| ∧ 2 ≤ |hi t + 10 * (u : ℝ)| ∧
      (u ≠ t → 0 < (lo t + 10 * (u : ℝ)) * (hi t + 10 * (u : ℝ))) := by
  unfold lo hi
  rcases lt_trichotomy u t with h | h | h
  · have hle : (u : ℝ) + 1 ≤ t := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    exact ⟨by linarith, by linarith, fun _ => mul_pos_of_neg_of_neg (by linarith) (by linarith)⟩
  · subst u
    have h₁ : -10 * (t : ℝ) - 3 + 10 * t = -3 := by ring
    have h₂ : -10 * (t : ℝ) + 3 + 10 * t = 3 := by ring
    rw [h₁, h₂]
    norm_num
  · have hle : (t : ℝ) + 1 ≤ u := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact ⟨by linarith, by linarith, fun _ => mul_pos (by linarith) (by linarith)⟩

private theorem paired_positive (t : ℕ) (xs : List ℕ) (h : t ∉ xs) :
    0 < diagProduct (lo t) xs * diagProduct (hi t) xs := by
  induction xs with
  | nil => simp [diagProduct]
  | cons u rest ih =>
    have hu : u ≠ t := by intro e; exact h (by simp [e])
    have ht : t ∉ rest := fun ht => h (List.mem_cons_of_mem _ ht)
    change 0 < ((_ * diagProduct (lo t) rest) * (_ * diagProduct (hi t) rest))
    rw [mul_mul_mul_comm]
    exact mul_pos ((end_bounds t u).2.2 hu) (ih ht)

private theorem paired_negative {t : ℕ} (xs : List ℕ) (hd : xs.Nodup) (ht : t ∈ xs) :
    diagProduct (lo t) xs * diagProduct (hi t) xs < 0 := by
  induction xs with
  | nil => simp at ht
  | cons u rest ih =>
    have hnod := List.nodup_cons.mp hd
    change (_ * diagProduct (lo t) rest) * (_ * diagProduct (hi t) rest) < 0
    rw [mul_mul_mul_comm]
    by_cases he : u = t
    · subst u
      have h₁ : lo t + 10 * (t : ℝ) = -3 := by unfold lo; ring
      have h₂ : hi t + 10 * (t : ℝ) = 3 := by unfold hi; ring
      change ((lo t + 10 * (t : ℝ)) * (hi t + 10 * (t : ℝ))) *
        (diagProduct (lo t) rest * diagProduct (hi t) rest) < 0
      rw [h₁, h₂]
      exact mul_neg_of_neg_of_pos (by norm_num) (paired_positive t rest hnod.1)
    · exact mul_neg_of_pos_of_neg ((end_bounds t u).2.2 he)
        (ih hnod.2 ((List.mem_cons.mp ht).resolve_left (Ne.symm he)))

/-- У каждого отличающегося диагонального центра имеется собственный корень
    в интервале радиуса 3. Доказывается сменой знака континуанта. -/
theorem root_in_each_bin {xs : List ℕ} (hd : xs.Nodup) {t : ℕ} (ht : t ∈ xs) :
    ∃ z : ℝ, (block xs).eval z = 0 ∧ |z + 10 * (t : ℝ)| ≤ 3 := by
  have hl := (dominant_block xs (lo t) (fun u _ => (end_bounds t u).1)).1
  have hr := (dominant_block xs (hi t) (fun u _ => (end_bounds t u).2.1)).1
  have hdia := paired_negative xs hd ht
  have hmul := mul_pos hl hr
  rw [mul_mul_mul_comm] at hmul
  have hop : (block xs).eval (lo t) * (block xs).eval (hi t) < 0 :=
    (mul_pos_iff.mp hmul).resolve_left (fun h => (not_lt_of_ge h.2.le) hdia) |>.1
  have hle : lo t ≤ hi t := by unfold lo hi; linarith
  have hzero : (0 : ℝ) ∈ (fun x => (block xs).eval x) '' Set.Icc (lo t) (hi t) := by
    rcases mul_neg_iff.mp hop with h | h
    · exact intermediate_value_Icc' hle (block xs).continuous.continuousOn ⟨h.2.le, h.1.le⟩
    · exact intermediate_value_Icc hle (block xs).continuous.continuousOn ⟨h.1.le, h.2.le⟩
  obtain ⟨z, ⟨hz₁, hz₂⟩, hz⟩ := hzero
  unfold lo at hz₁
  unfold hi at hz₂
  exact ⟨z, hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem block_natDegree (xs : List ℕ) : (block xs).natDegree = xs.length := by
  simp only [block, intervalCharpoly_natDegree, List.length_map]

theorem block_monic (xs : List ℕ) : (block xs).Monic := Matrix.charpoly_monic _

/-- Имеются ровно n различных вещественных корней; каждый встречается один раз. -/
theorem simple_real_spectrum (xs : List ℕ) (hd : xs.Nodup) :
    (block xs).roots.card = xs.length ∧ (block xs).roots.Nodup := by
  classical
  let labels := xs.toFinset
  have hroot (a : labels) := root_in_each_bin hd (t := (a : ℕ)) (List.mem_toFinset.mp a.prop)
  choose f hf hbin using hroot
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact different_centres (hbin a) (hab ▸ hbin b)
  have hsub : Finset.univ.image f ⊆ (block xs).roots.toFinset := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((mem_roots (block_monic xs).ne_zero).mpr (hf a))
  have h₁ := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_coe,
    show labels.card = xs.length from List.toFinset_card_of_nodup hd] at h₁
  have h₂ := Multiset.toFinset_card_le (block xs).roots
  have h₃ := card_roots' (block xs)
  rw [block_natDegree] at h₃
  exact ⟨by omega, Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)⟩

theorem coprime_of_distinct_zeros {xs : List ℕ} (hd : xs.Nodup)
    (q : ℝ[X]) (h : ∀ z, (block xs).eval z = 0 → q.eval z ≠ 0) : IsCoprime (block xs) q := by
  have hcard := (simple_real_spectrum xs hd).1.trans (block_natDegree xs).symm
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (block_monic xs) hcard
  rw [← hfac]
  suffices hall : ∀ m : Multiset ℝ, (∀ z ∈ m, q.eval z ≠ 0) →
      IsCoprime (m.map (fun z => X - C z)).prod q by
    exact hall _ (fun z hz => h z (isRoot_of_mem_roots hz))
  intro m
  induction m using Multiset.induction_on with
  | empty => intro _; simpa only [Multiset.map_zero, Multiset.prod_zero] using
      (isCoprime_one_left : IsCoprime (1 : ℝ[X]) q)
  | cons a m ih =>
    intro hm
    rw [Multiset.map_cons, Multiset.prod_cons]
    apply IsCoprime.mul_left
    · apply (irreducible_X_sub_C a).coprime_iff_not_dvd.mpr
      exact fun hx => hm a (by simp) (dvd_iff_isRoot.mp hx)
    · exact ih (fun z hz => hm z (Multiset.mem_cons_of_mem hz))

/-- Разделённые блоки взаимно просты как многочлены над ℝ. -/
theorem separated_coprime {xs ys : List ℕ} (hd : xs.Nodup) (hxy : xs.Disjoint ys) :
    IsCoprime (block xs) (block ys) :=
  coprime_of_distinct_zeros hd _ (fun _ h => separated_real_roots hxy h)

theorem cut (left right : List ℕ) (u v : ℕ) :
    block (left ++ u :: v :: right) =
      block (left ++ [u]) * block (v :: right) - block left * block right := by
  simpa only [block, List.map_append, List.map_cons, List.map_nil, site, PathSite.weight,
    one_mul, map_one] using
    (charpoly_cut (left.map site) (right.map site) (site u) (site v))

theorem adjacent_tail (xs : List ℕ) (u : ℕ) (z : ℝ) (hu : (block (u :: xs)).eval z = 0) :
    (block xs).eval z ≠ 0 := by
  induction xs generalizing u with
  | nil => simp
  | cons v tail ih =>
    intro hv
    rw [block_step] at hu
    have ht : (block tail).eval z = 0 := by simpa [hv] using hu
    exact ih v hv ht

private theorem adjacent_prefix (xs : List ℕ) (u : ℕ) (z : ℝ)
    (hu : (block (xs ++ [u])).eval z = 0) : (block xs).eval z ≠ 0 := by
  induction xs using List.reverseRecOn generalizing u with
  | nil => simp
  | append_singleton left v ih =>
    intro hv
    rw [List.append_assoc] at hu
    change (block (left ++ v :: u :: [])).eval z = 0 at hu
    rw [cut] at hu
    have ht : (block left).eval z = 0 := by simpa [hv] using hu
    exact ih v hv ht

/-- Ни один корень всего блока не зануляет определитель слева от отмеченной
    вершины: в противном случае обе разделённые ветви имели бы общий корень. -/
theorem full_root_prefix_ne {left right : List ℕ} {j : ℕ}
    (hsep : left.Disjoint right) {z : ℝ} (hz : (block (left ++ j :: right)).eval z = 0) :
    (block left).eval z ≠ 0 := by
  induction left using List.reverseRecOn with
  | nil => simp
  | append_singleton prev u _ =>
    intro hl
    have hp := adjacent_prefix prev u z hl
    have hr := separated_real_roots hsep hl
    rw [List.append_assoc] at hz
    change (block (prev ++ u :: j :: right)).eval z = 0 at hz
    rw [cut] at hz
    have hprod : (block prev).eval z * (block right).eval z = 0 := by
      simpa only [eval_sub, eval_mul, hl, zero_mul, zero_sub, neg_eq_zero] using hz
    exact mul_ne_zero hp hr hprod

/-- Вложенные правые многочлены W,U тоже взаимно просты. -/
theorem nested_coprime {middle right : List ℕ} (k : ℕ) (hd : right.Nodup)
    (hdis : middle.Disjoint right) : IsCoprime (block (middle ++ k :: right)) (block right) := by
  apply IsCoprime.symm
  apply coprime_of_distinct_zeros hd
  intro z hr
  cases right with
  | nil => simp at hr
  | cons u tail =>
    have hm := separated_real_roots hdis.symm hr
    have ht := adjacent_tail tail u z hr
    rw [cut]
    simpa only [eval_sub, eval_mul, hr, mul_zero, zero_sub, neg_ne_zero] using mul_ne_zero hm ht

private theorem unit_weights (xs : List ℕ) : edgeProduct (xs.map site) = 1 := by
  induction xs with
  | nil => simp [edgeProduct]
  | cons t xs ih =>
    change (site t).weight * edgeProduct (xs.map site) = 1
    simp [ih, site, PathSite.weight]

theorem block_condensation (left middle right : List ℕ) (j k : ℕ) :
    block (left ++ j :: (middle ++ k :: right)) * block middle =
      block (middle ++ k :: right) * block (left ++ j :: middle) - block right * block left := by
  have h := charpoly_condensation (left.map site) (middle.map site) (right.map site) (site j) (site k)
  have hk : (site j).weight * edgeProduct (middle.map site) = 1 := by
    simp [unit_weights, site, PathSite.weight]
  rw [hk, map_one, one_mul] at h
  simpa only [block, List.map_append, List.map_cons] using h

/-- Общий спектральный корень из §5 для конкретной полной матрицы J₀.
    Предпосылки о спектре, взаимной простоте и числе корней доказаны выше.
    Для концeвого входа остаются лишь невырожденная разметка и порог длин. -/
theorem concrete_common_spectral_root (left middle right : List ℕ) (j k : ℕ)
    (hlabels : (left ++ j :: (middle ++ k :: right)).Nodup)
    (hleft : 0 < left.length) (hthreshold : left.length ≤ right.length + 2) :
    let D := block (left ++ j :: (middle ++ k :: right))
    let B := block middle
    let W := block (middle ++ k :: right)
    let U := block right
    let E := block left
    ∃ x ∈ D.roots.toFinset, ∀ v : SpectralVariation D B W U E E (1 : ℝ),
      v.dE.eval x = 0 → v.dH.eval x = 0 →
        v.dK = 0 ∧ v.dB = 0 ∧ v.dP = 0 ∧ v.dH = 0 ∧ v.dE = 0 := by
  classical
  let full := left ++ j :: (middle ++ k :: right)
  let throughJ := left ++ j :: middle
  have hp : (throughJ ++ k :: right).Nodup := by
    simpa [throughJ, List.append_assoc] using hlabels
  have hlefts := List.nodup_append.mp hlabels
  have hrights := List.nodup_cons.mp hlefts.2.1
  have hmids := List.nodup_append.mp hrights.2
  have hdR := (List.nodup_cons.mp hmids.2.1).2
  have hLW : left.Disjoint (middle ++ k :: right) :=
    fun a ha hb => hlefts.2.2 ha (List.mem_cons_of_mem _ hb)
  have hLM : left.Disjoint middle := fun a ha hb => hLW ha (List.mem_append_left _ hb)
  have hMR : middle.Disjoint right :=
    fun a ha hb => hmids.2.2 ha (List.mem_cons_of_mem _ hb)
  have hLR : throughJ.Disjoint right :=
    fun a ha hb => (List.nodup_append.mp hp).2.2 ha (List.mem_cons_of_mem _ hb)
  let spec := (block full).roots.toFinset
  have hsimp := simple_real_spectrum full hlabels
  have hspec : spec.card = full.length :=
    (Multiset.toFinset_card_of_nodup hsimp.2).trans hsimp.1
  have hroots (x : ℝ) (hx : x ∈ spec) :
      (block full).eval x = 0 ∧ (block left).eval x ≠ 0 ∧ (block throughJ).eval x ≠ 0 := by
    have hd : (block full).eval x = 0 := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
    have hd' : (block (throughJ ++ k :: right)).eval x = 0 := by
      simpa [throughJ, full, List.append_assoc] using hd
    exact ⟨hd, full_root_prefix_ne hLW hd, full_root_prefix_ne hLR hd'⟩
  apply exists_common_spectral_root (k := (1 : ℝ)) one_ne_zero (by simp)
    (block_monic left) _ (block_monic _).ne_zero (nested_coprime k hdR hMR)
    (separated_coprime hlefts.1 hLM) (separated_coprime hlefts.1 hLW)
    (block_condensation left middle right j k) _ spec _ hroots
  · rwa [block_natDegree]
  · simp only [block_natDegree, List.length_append, List.length_cons]; omega
  · rw [block_natDegree, hspec]
    simp [full]

def shiftedSite (z : ℝ) (t : ℕ) : PathSite ℝ := ⟨z + 10 * (t : ℝ), -1, -1⟩

theorem eval_as_cont (z : ℝ) : ∀ xs : List ℕ,
    (block xs).eval z = cont (xs.map (shiftedSite z))
  | [] => by simp
  | [t] => by simp [site, shiftedSite]
  | t :: u :: xs => by
    rw [block_step, eval_sub, eval_mul, eval_sub, eval_X, eval_C, eval_as_cont z (u :: xs),
      eval_as_cont z xs]
    simp only [List.map_cons, cont_cons_cons, shiftedSite, site, PathSite.weight]
    ring

theorem shifted_directed (xs : List ℕ) (z : ℝ) :
    directedProduct (xs.map (shiftedSite z)) = 1 := by
  induction xs with
  | nil => simp [directedProduct]
  | cons t xs ih =>
    change -((shiftedSite z t).lower) * directedProduct (xs.map (shiftedSite z)) = 1
    simp [ih, shiftedSite]

theorem shifted_symm (xs : List ℕ) (z : ℝ) :
    (pathMatrix (xs.map (shiftedSite z))).transpose = pathMatrix (xs.map (shiftedSite z)) := by
  have hmap : (xs.map (shiftedSite z)).map swapSite = xs.map (shiftedSite z) := by
    rw [List.map_map]
    rfl
  funext i j
  change entry (xs.map (shiftedSite z)) j.val i.val = entry (xs.map (shiftedSite z)) i.val j.val
  exact (entry_swap _ i.val j.val).symm.trans
    (congrArg (fun a : List (PathSite ℝ) => entry a i.val j.val) hmap)

private theorem kernel_coordinate (xs : List (PathSite ℝ)) (v : Fin xs.length → ℝ)
    (hs : (pathMatrix xs).transpose = pathMatrix xs) (hv : (pathMatrix xs).mulVec v = 0)
    (i : Fin xs.length) :
    v i * directedProduct (xs.take i.val) =
      v ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩ * cont (xs.take i.val) := by
  classical
  let e : Fin xs.length := ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩
  let pre := xs.take i.val
  let g : Fin xs.length → ℝ := fun j => firstNumerator pre j.val
  have padded (k : Fin xs.length) :
      (pathMatrix xs).mulVec g k = (if k.val = 0 then cont pre else 0) -
        (if k.val = pre.length then directedProduct pre else 0) := by
    change (pathMatrix xs).mulVec (fun j => firstNumerator pre j.val) k = _
    have heq : pre ++ xs.drop i.val = xs := List.take_append_drop _ _
    generalize hn : pre = p at heq ⊢
    generalize hm : xs.drop i.val = r at heq
    revert k
    rw [← heq]
    exact mulVec_padded_prefix p r
  have hg : (pathMatrix xs).mulVec g =
      Pi.single e (cont pre) - Pi.single i (directedProduct pre) := by
    funext k
    rw [padded]
    have hlen : pre.length = i.val := by simp [pre, Nat.le_of_lt i.isLt]
    have he : k = e ↔ k.val = 0 := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    have hi : k = i ↔ k.val = i.val := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    simp only [Pi.sub_apply, Pi.single_apply, hlen, he, hi]
  have hleft := Matrix.vecMul_transpose (pathMatrix xs) v
  rw [hs, hv] at hleft
  have hd : dotProduct v ((pathMatrix xs).mulVec g) = 0 := by
    rw [Matrix.dotProduct_mulVec, hleft, zero_dotProduct]
  rw [hg, dotProduct_sub, dotProduct_single, dotProduct_single, sub_eq_zero] at hd
  exact hd.symm

/-- На спектральной точке любая ненулевая колонка ядра zI−J имеет только
    ненулевые координаты; индекс может быть произвольной вершиной. -/
theorem pencil_kernel_nowhere_zero (xs : List ℕ) (hlabels : xs.Nodup) (z : ℝ)
    (v : Fin (xs.map (shiftedSite z)).length → ℝ) (hv : v ≠ 0)
    (hker : (pathMatrix (xs.map (shiftedSite z))).mulVec v = 0) :
    ∀ i, v i ≠ 0 := by
  classical
  have hdet : (pathMatrix (xs.map (shiftedSite z))).det = 0 := by
    by_contra h
    have he := congrArg (fun w => (pathMatrix (xs.map (shiftedSite z)))⁻¹.mulVec w) hker
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h),
      Matrix.one_mulVec, Matrix.mulVec_zero] at he
    exact hv he
  have hz : (block xs).eval z = 0 := by
    rwa [eval_as_cont, ← det_eq_cont]
  intro i
  let e : Fin (xs.map (shiftedSite z)).length := ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩
  have hform (j : Fin (xs.map (shiftedSite z)).length) :
      v j = v e * (block (xs.take j.val)).eval z := by
    have h := kernel_coordinate (xs.map (shiftedSite z)) v (shifted_symm xs z) hker j
    rw [← List.map_take, shifted_directed, mul_one, ← eval_as_cont] at h
    exact h
  have he : v e ≠ 0 := by
    intro hh
    apply hv
    funext j
    rw [hform j, hh, zero_mul, Pi.zero_apply]
  have hi : i.val < xs.length := by simpa only [List.length_map] using i.isLt
  have hsplit : xs.take i.val ++ xs[i.val] :: xs.drop (i.val + 1) = xs := by
    rw [List.getElem_cons_drop hi, List.take_append_drop]
  have hl : (xs.take i.val).Disjoint (xs.drop (i.val + 1)) := by
    have hn : (xs.take i.val ++ xs[i.val] :: xs.drop (i.val + 1)).Nodup := by
      rw [hsplit]; exact hlabels
    exact fun t ht hr => (List.nodup_append.mp hn).2.2 ht (List.mem_cons_of_mem _ hr)
  have hp := full_root_prefix_ne (j := xs[i.val]) hl (by rw [hsplit]; exact hz)
  rw [hform i]
  exact mul_ne_zero he hp

private theorem shifted_entry (xs : List ℕ) (z : ℝ) (i j : ℕ) (hi : i < xs.length) :
    entry (xs.map (shiftedSite z)) i j = (if i = j then z else 0) - entry (xs.map site) i j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons u xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => simp [entry, site, shiftedSite]
      | succ j => by_cases h : j = 0 <;> simp [entry, site, shiftedSite, h]
    | succ i =>
      cases j with
      | zero => by_cases h : i = 0 <;> simp [entry, site, shiftedSite, h]
      | succ j =>
        simpa only [List.map_cons, entry, Nat.succ.injEq] using ih i j (Nat.lt_of_succ_lt_succ hi)

/-- У каждого собственного вектора самой симметричной матрицы J₀ все
    координаты ненулевые. Предполагаются только разметка без повторений,
    уравнение J₀v=zv и ненулевой вектор v. -/
theorem eigenvector_nowhere_zero (xs : List ℕ) (hd : xs.Nodup) (z : ℝ)
    (v : Fin (xs.map site).length → ℝ) (hv : v ≠ 0)
    (he : (pathMatrix (xs.map site)).mulVec v = z • v) : ∀ i, v i ≠ 0 := by
  classical
  let e : Fin (xs.map (shiftedSite z)).length ≃ Fin (xs.map site).length := finCongr (by simp)
  have hmat : pathMatrix (xs.map (shiftedSite z)) =
      z • (1 : Matrix _ _ ℝ) - (pathMatrix (xs.map site)).submatrix e e := by
    funext i j
    have hi : i.val < xs.length := by simpa only [List.length_map] using i.isLt
    have h := shifted_entry xs z i.val j.val hi
    by_cases hij : i = j
    · subst j
      simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.submatrix_apply,
        pathMatrix, e] using h
    · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.submatrix_apply,
        pathMatrix, e, hij, hne] using h
  have hv' : v ∘ e ≠ 0 := by
    intro h
    apply hv
    funext i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using
      congrFun h (e.symm i)
  have hker : (pathMatrix (xs.map (shiftedSite z))).mulVec (v ∘ e) = 0 := by
    rw [hmat, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
      Matrix.submatrix_mulVec_equiv]
    have hfun : (v ∘ e) ∘ e.symm = v := by funext i; simp
    rw [hfun, he, sub_eq_zero]
    rfl
  have h := pencil_kernel_nowhere_zero xs hd z (v ∘ e) hv' hker
  intro i
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h (e.symm i)

/-- При положительных метках весь спектр строго отрицателен. -/
theorem negative_root {xs : List ℕ} (hpos : ∀ t ∈ xs, 0 < t) {z : ℝ}
    (hz : (block xs).eval z = 0) : z < 0 := by
  obtain ⟨t, ht, hb⟩ := real_root_near_label hz
  have hp : (1 : ℝ) ≤ t := by exact_mod_cast hpos t ht
  linarith [(abs_lt.mp hb).2]

/-- При неотрицательном сдвиге каждый интервальный определитель в точке z
    положителен. -/
theorem positive_on_ray {xs : List ℕ} (hpos : ∀ t ∈ xs, 0 < t) {z : ℝ} (hz : 0 ≤ z) :
    0 < (block xs).eval z := by
  have hdiag (t : ℕ) (ht : t ∈ xs) : 2 ≤ z + 10 * (t : ℝ) := by
    have hp : (1 : ℝ) ≤ t := by exact_mod_cast hpos t ht
    linarith
  have hd := (dominant_block xs z (fun t ht => (hdiag t ht).trans (le_abs_self _))).1
  have aux (ys : List ℕ) (h : ∀ t ∈ ys, 0 < z + 10 * (t : ℝ)) : 0 < diagProduct z ys := by
    induction ys with
    | nil => simp [diagProduct]
    | cons t ys ih => exact mul_pos (h t (by simp)) (ih (fun a ha => h a (by simp [ha])))
  have hprod := aux xs (fun t ht => lt_of_lt_of_le (by norm_num) (hdiag t ht))
  exact pos_of_mul_pos_left hd hprod.le

/-- Матрица с диагональю −10,−20,…,−10n и рёбрами 1 обладает в точности
    n отрицательными простыми вещественными корнями, а каждый собственный
    вектор ненулевой во всех координатах. -/
theorem standard_witness (n : ℕ) :
    let xs := List.range' 1 n
    (block xs).roots.card = n ∧ (block xs).roots.Nodup ∧
      (∀ z ∈ (block xs).roots, z < 0) ∧
      ∀ (z : ℝ) (v : Fin (xs.map site).length → ℝ), v ≠ 0 →
        (pathMatrix (xs.map site)).mulVec v = z • v → ∀ i, v i ≠ 0 := by
  dsimp only
  have hn := List.nodup_range' (s := 1) (n := n)
  have hc := simple_real_spectrum _ hn
  refine ⟨by simpa only [List.length_range'] using hc.1, hc.2, ?_, ?_⟩
  · intro z hz
    exact negative_root (fun t ht => List.left_le_of_mem_range' ht) (isRoot_of_mem_roots hz)
  · exact fun z v hv he => eigenvector_nowhere_zero _ hn z v hv he

end Catenary.Spectral
