import Chain.Continuant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The first input column of a tridiagonal resolvent is obtained by
solving the actual matrix equation. The identity before division holds
even when the matrix is singular. -/

namespace Catenary.Continuant

variable {R : Type*} [CommRing R]

/-- Numerator of the entry in row `i` of the first inverse column. -/
def firstNumerator : List (PathSite R) → Nat → R
  | [], _ => 0
  | _ :: xs, 0 => cont xs
  | a :: xs, i + 1 => -a.lower * firstNumerator xs i

theorem firstNumerator_at_split (before after_ : List (PathSite R)) (v : PathSite R) :
    firstNumerator (before ++ v :: after_) before.length =
      (before.map (fun a => -a.lower)).prod * cont after_ := by
  induction before with
  | nil => simp [firstNumerator]
  | cons a before ih =>
      simp only [List.cons_append, List.length_cons, firstNumerator, List.map_cons,
        List.prod_cons, ih, mul_assoc]

/-- Multiplying the putative inverse column by the tridiagonal matrix
produces `det(M) e₁`, without division. -/
theorem mulVec_firstNumerator (xs : List (PathSite R)) (i : Fin xs.length) :
    (pathMatrix xs).mulVec (fun j => firstNumerator xs j.val) i =
      if i.val = 0 then cont xs else 0 := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons a xs ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · cases xs with
        | nil =>
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pathMatrix, entry,
              firstNumerator]
        | cons b tail =>
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pathMatrix, entry,
              firstNumerator, cont_cons_cons, PathSite.weight]
            ring
      · have h := ih k
        simp only [Matrix.mulVec, dotProduct, pathMatrix] at h ⊢
        change (∑ x : Fin (xs.length + 1), entry (a :: xs) (k.val + 1) x.val *
          firstNumerator (a :: xs) x.val) = _
        rw [Fin.sum_univ_succ (fun x : Fin (xs.length + 1) =>
          entry (a :: xs) (k.val + 1) x.val * firstNumerator (a :: xs) x.val)]
        simp only [Fin.val_succ, Fin.val_zero, entry, firstNumerator, Nat.succ_ne_zero, if_false]
        have hs : (∑ j : Fin xs.length,
              entry xs k.val j.val * (-a.lower * firstNumerator xs j.val)) =
            -a.lower * ∑ j : Fin xs.length, entry xs k.val j.val * firstNumerator xs j.val := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hs, h]
        split <;> simp_all

section Field

variable {K : Type*} [Field K]

/-- The first column of the actual inverse matrix at every nonsingular
spectral value. Apply to the entries of (sI-J). -/
theorem inv_first_column (a : PathSite K) (xs : List (PathSite K))
    (i : Fin (a :: xs).length) (h : cont (a :: xs) ≠ 0) :
    (pathMatrix (a :: xs))⁻¹ i (0 : Fin (xs.length + 1)) =
      firstNumerator (a :: xs) i.val / cont (a :: xs) := by
  classical
  letI : NeZero (a :: xs).length := ⟨by simp⟩
  let M := pathMatrix (a :: xs)
  let g : Fin (a :: xs).length → K := fun j => firstNumerator (a :: xs) j.val
  have hd : (pathMatrix (a :: xs)).det ≠ 0 := by rw [det_eq_cont]; exact h
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hd
  have hg : M.mulVec g = Pi.single 0 (cont (a :: xs)) := by
    funext k
    rw [show M.mulVec g k = _ from mulVec_firstNumerator (a :: xs) k]
    by_cases hk : k = 0
    · subst k
      simp
    · have hv : k.val ≠ 0 := fun e => hk (Fin.ext e)
      simp [Pi.single_apply, hk, Ne.symm hk, hv]
  have id := congrArg (fun w => M⁻¹.mulVec w) hg
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu, Matrix.one_mulVec,
    Matrix.mulVec_single] at id
  apply (eq_div_iff h).2
  exact (congrFun id i).symm

end Field
end Catenary.Continuant
