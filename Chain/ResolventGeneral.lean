import Chain.Resolvent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SplitIfs

/-! An arbitrary input is recovered from an endpoint column by applying
the whole matrix to a zero-extended solution on the prefix. -/

namespace Catenary.Continuant

variable {R : Type*} [CommRing R]

def directedProduct (xs : List (PathSite R)) : R := (xs.map fun a => -a.lower).prod

def swapSite (a : PathSite R) : PathSite R := ⟨a.diag, a.lower, a.upper⟩

private theorem run_swap (xs : List (PathSite R)) (v : R × R) :
    run (xs.map swapSite) v = run xs v := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [run, ih, step, swapSite, PathSite.weight, mul_comm]

@[simp] theorem cont_swap (xs : List (PathSite R)) : cont (xs.map swapSite) = cont xs :=
  congrArg Prod.fst (run_swap xs (1,0))

theorem entry_swap (xs : List (PathSite R)) (i j : Nat) :
    entry (xs.map swapSite) i j = entry xs j i := by
  induction xs generalizing i j with
  | nil => rfl
  | cons a xs ih =>
      cases i <;> cases j <;> simp [entry, swapSite, ih]

theorem firstNumerator_past (xs : List (PathSite R)) (idx : Nat) (h : xs.length ≤ idx) :
    firstNumerator xs idx = 0 := by
  induction xs generalizing idx with
  | nil => rfl
  | cons a xs ih =>
      cases idx with
      | zero => simp at h
      | succ idx =>
          simp only [firstNumerator]
          rw [ih idx (by simpa using h), mul_zero]

theorem firstNumerator_prefix (before after_ : List (PathSite R)) (idx : Nat) :
    firstNumerator (before ++ after_) (before.length + idx) =
      directedProduct before * firstNumerator after_ idx := by
  induction before with
  | nil => simp [directedProduct]
  | cons a before ih =>
      simp only [List.cons_append, List.length_cons, Nat.succ_add, firstNumerator, ih,
        directedProduct, List.map_cons, List.prod_cons, mul_assoc]

/-- Extension by zero of the numerator vector of a prefix. Apart from the
endpoint and the first vertex after the cut its image is zero. The empty
prefix is included (the two terms then cancel). -/
theorem mulVec_padded_prefix (before after_ : List (PathSite R)) (i : Fin (before ++ after_).length) :
    (pathMatrix (before ++ after_)).mulVec (fun j => firstNumerator before j.val) i =
      (if i.val = 0 then cont before else 0) -
      (if i.val = before.length then directedProduct before else 0) := by
  induction before with
  | nil => simp [firstNumerator, directedProduct, Matrix.mulVec, dotProduct]
  | cons a before ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · cases before with
        | nil =>
            cases after_ with
            | nil =>
                simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pathMatrix, entry,
                  firstNumerator]
            | cons h rest =>
                simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pathMatrix, entry,
                  firstNumerator]
        | cons b rest =>
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pathMatrix, entry,
              firstNumerator, cont_cons_cons, PathSite.weight]
            ring
      · have h := ih k
        simp only [Matrix.mulVec, dotProduct, pathMatrix, List.cons_append] at h ⊢
        change (∑ x : Fin ((before ++ after_).length + 1),
          entry (a :: (before ++ after_)) (k.val + 1) x.val * firstNumerator (a :: before) x.val) = _
        rw [Fin.sum_univ_succ (fun x : Fin ((before ++ after_).length + 1) =>
          entry (a :: (before ++ after_)) (k.val + 1) x.val * firstNumerator (a :: before) x.val)]
        simp only [Fin.val_succ, Fin.val_zero, entry, firstNumerator, Nat.succ_ne_zero,
          if_false, List.length_cons, Nat.succ.injEq, zero_sub]
        have hs : (∑ j : Fin (before ++ after_).length,
              entry (before ++ after_) k.val j.val * (-a.lower * firstNumerator before j.val)) =
            -a.lower * ∑ j : Fin (before ++ after_).length,
              entry (before ++ after_) k.val j.val * firstNumerator before j.val := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hs, h]
        simp only [directedProduct, List.map_cons, List.prod_cons]
        split_ifs <;> ring

section Field

variable {K : Type*} [Field K]

private theorem inv_first_at (xs : List (PathSite K)) (z t : Fin xs.length)
    (hz : z.val = 0) (h : cont xs ≠ 0) :
    (pathMatrix xs)⁻¹ t z = firstNumerator xs t.val / cont xs := by
  cases xs with
  | nil => exact Fin.elim0 z
  | cons a xs =>
      have eq : z = (0 : Fin (xs.length + 1)) := Fin.ext hz
      subst z
      exact inv_first_column a xs t h

/-- Entry in any row weakly to the right of the input. The prefix edge
product is nonzero for a bidirected chain with nonzero rates. No principal
minor other than the determinant of the full matrix is inverted. -/
theorem inv_from_input (before : List (PathSite K)) (a : PathSite K) (after_ : List (PathSite K))
    (v : Fin (a :: after_).length)
    (hD : cont (before ++ a :: after_) ≠ 0) (hp : directedProduct before ≠ 0) :
    let N := (before ++ a :: after_).length
    let s : Fin N := ⟨before.length, by simp [N]⟩
    let t : Fin N := ⟨before.length + v.val, by simp [N]⟩
    (pathMatrix (before ++ a :: after_))⁻¹ t s =
      cont before * firstNumerator (a :: after_) v.val / cont (before ++ a :: after_) := by
  classical
  intro N s t
  let z : Fin N := ⟨0, by simp [N]⟩
  let M := pathMatrix (before ++ a :: after_)
  let g : Fin N → K := fun j => firstNumerator before j.val
  have hd : (pathMatrix (before ++ a :: after_)).det ≠ 0 := by rw [det_eq_cont]; exact hD
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hd
  have hg : M.mulVec g = Pi.single z (cont before) - Pi.single s (directedProduct before) := by
    funext k
    change (pathMatrix (before ++ a :: after_)).mulVec (fun j => firstNumerator before j.val) k = _
    rw [mulVec_padded_prefix]
    have hz : k = z ↔ k.val = 0 := ⟨fun e => congrArg Fin.val e, fun e => Fin.ext e⟩
    have hs : k = s ↔ k.val = before.length := ⟨fun e => congrArg Fin.val e, fun e => Fin.ext e⟩
    simp only [Pi.sub_apply, Pi.single_apply]
    by_cases p : k = z <;> by_cases q : k = s <;> simp_all
  have eqn := congrArg (fun w => M⁻¹.mulVec w) hg
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu, Matrix.one_mulVec,
    Matrix.mulVec_sub, Matrix.mulVec_single] at eqn
  have atRow := congrFun eqn t
  change firstNumerator before (before.length + v.val) =
    M⁻¹ t z * cont before - M⁻¹ t s * directedProduct before at atRow
  have hzcol : M⁻¹ t z =
      directedProduct before * firstNumerator (a :: after_) v.val / cont (before ++ a :: after_) := by
    rw [show M⁻¹ t z = _ from inv_first_at (before ++ a :: after_) z t rfl hD]
    change firstNumerator _ (before.length + v.val) / _ = _
    rw [firstNumerator_prefix]
  rw [firstNumerator_past _ _ (by omega), hzcol] at atRow
  field_simp [hD] at atRow
  apply (eq_div_iff hD).2
  apply mul_right_cancel₀ hp
  linear_combination atRow

/-- The corresponding formula when the output is on the left. The
directed edge factors now use the upper entries of the original matrix. -/
theorem inv_to_left (before : List (PathSite K)) (a : PathSite K) (after_ : List (PathSite K))
    (v : Fin (a :: after_).length)
    (hD : cont (before ++ a :: after_) ≠ 0) (hp : directedProduct (before.map swapSite) ≠ 0) :
    let N := (before ++ a :: after_).length
    let s : Fin N := ⟨before.length, by simp [N]⟩
    let t : Fin N := ⟨before.length + v.val, by simp [N]⟩
    (pathMatrix (before ++ a :: after_))⁻¹ s t =
      cont before * firstNumerator ((a :: after_).map swapSite) v.val / cont (before ++ a :: after_) := by
  classical
  intro N s t
  let F := before ++ a :: after_
  let F' := before.map swapSite ++ swapSite a :: after_.map swapSite
  have hs : F' = F.map swapSite := by simp [F, F']
  let e : Fin N ≃ Fin F'.length := finCongr (by simp [N,F'])
  have hm : (pathMatrix F).transpose = Matrix.reindex e.symm e.symm (pathMatrix F') := by
    funext i j
    change entry F j.val i.val = entry F' i.val j.val
    rw [hs, entry_swap]
  have hi : (pathMatrix F)⁻¹ s t = (pathMatrix F')⁻¹ (e t) (e s) := by
    change ((pathMatrix F)⁻¹).transpose t s = _
    rw [Matrix.transpose_nonsing_inv, hm, Matrix.inv_reindex]
    rfl
  rw [hi]
  let v' : Fin (swapSite a :: after_.map swapSite).length := ⟨v.val, by simp⟩
  have hd : cont F' ≠ 0 := by rw [hs, cont_swap]; exact hD
  have h := inv_from_input (before.map swapSite) (swapSite a) (after_.map swapSite) v' hd hp
  dsimp only at h
  have se : e s = (⟨(before.map swapSite).length, by simp [F']⟩ : Fin F'.length) :=
    Fin.ext (by simp [e,s])
  have te : e t = (⟨(before.map swapSite).length + v'.val, by simp [F',v']⟩ : Fin F'.length) :=
    Fin.ext (by simp [e,t,v'])
  rw [se, te]
  have hc : cont F' = cont F := by rw [hs, cont_swap]
  change (pathMatrix F')⁻¹ _ _ =
    cont (before.map swapSite) * firstNumerator (swapSite a :: after_.map swapSite) v'.val /
      cont F' at h
  rw [cont_swap, hc] at h
  exact h

end Field
end Catenary.Continuant
