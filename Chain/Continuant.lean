import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Finite tridiagonal chains and their continuants

A site holds its diagonal and the two matrix entries on the edge to its
right. The last site's edge entries are ignored. All results apply over a
commutative ring, including the polynomial ring of the spectral pencil.
-/

namespace Catenary

structure PathSite (R : Type*) where
  diag : R
  upper : R
  lower : R

namespace PathSite

variable {R : Type*} [CommRing R]

def weight (a : PathSite R) : R := a.upper * a.lower

end PathSite

namespace Continuant

variable {R : Type*} [CommRing R]

/-- The one-site transfer takes the two succeeding suffix continuants
to the current suffix continuant and its successor. -/
def step (a : PathSite R) (v : R × R) : R × R :=
  (a.diag * v.1 - a.weight * v.2, v.1)

def run : List (PathSite R) → R × R → R × R
  | [], v => v
  | a :: xs, v => step a (run xs v)

def cont (xs : List (PathSite R)) : R := (run xs (1, 0)).1

def edgeProduct (xs : List (PathSite R)) : R := (xs.map PathSite.weight).prod

@[simp] theorem cont_nil : cont ([] : List (PathSite R)) = 1 := rfl

@[simp] theorem cont_singleton (a : PathSite R) : cont [a] = a.diag := by
  simp [cont, run, step]

theorem cont_cons_cons (a b : PathSite R) (xs : List (PathSite R)) :
    cont (a :: b :: xs) = a.diag * cont (b :: xs) - a.weight * cont xs := rfl

theorem run_append (xs ys : List (PathSite R)) (v : R × R) :
    run (xs ++ ys) v = run xs (run ys v) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, run, ih]

private theorem linear_run (xs : List (PathSite R)) (a b : R) (v w : R × R) :
    run xs (a * v.1 + b * w.1, a * v.2 + b * w.2) =
      (a * (run xs v).1 + b * (run xs w).1,
       a * (run xs v).2 + b * (run xs w).2) := by
  induction xs with
  | nil => rfl
  | cons h xs ih =>
      simp only [run, ih, step]
      congr 1
      ring

private theorem first_coordinates (xs : List (PathSite R)) (v : R × R) :
    (run xs v).1 =
      v.1 * (run xs (1, 0)).1 + v.2 * (run xs (0, 1)).1 := by
  simpa using congrArg Prod.fst (linear_run xs v.1 v.2 (1, 0) (0, 1))

private def wedge (v w : R × R) : R := v.1 * w.2 - w.1 * v.2

private theorem wedge_step (h : PathSite R) (v w : R × R) :
    wedge (step h v) (step h w) = h.weight * wedge v w := by
  simp only [wedge, step]
  ring

private theorem wedge_run (xs : List (PathSite R)) (v w : R × R) :
    wedge (run xs v) (run xs w) = edgeProduct xs * wedge v w := by
  induction xs with
  | nil => simp [run, edgeProduct]
  | cons h xs ih =>
      simp only [run, wedge_step, ih, edgeProduct, List.map_cons, List.prod_cons, mul_assoc]

private theorem first_wedge (xs : List (PathSite R)) (v w : R × R) :
    (run xs w).1 * v.1 - w.1 * (run xs v).1 = (run xs (0, 1)).1 * wedge v w := by
  rw [first_coordinates xs w, first_coordinates xs v]
  unfold wedge
  ring

private theorem last_edge (xs : List (PathSite R)) (j : PathSite R) :
    (run (xs ++ [j]) (0, 1)).1 = -j.weight * cont xs := by
  rw [run_append]
  change (run xs (j.diag * 0 - j.weight * 1, 0)).1 = _
  rw [first_coordinates]
  simp [cont]

/-- Splitting a chain across a single edge. -/
theorem cut (left right : List (PathSite R)) (j k : PathSite R) :
    cont (left ++ j :: k :: right) = cont (left ++ [j]) * cont (k :: right) -
      j.weight * cont left * cont right := by
  have h := first_coordinates (left ++ [j]) (run (k :: right) (1, 0))
  rw [last_edge] at h
  simp only [cont, run_append, run, step] at h ⊢
  linear_combination h

/-- For the two marked sites `j`, `k`, the full determinant times the
interior determinant equals the product of the two single-cut determinants
minus the product of all intervening edge weights and the two outer
determinants. Empty outer and interior segments are included. -/
theorem condensation (left middle right : List (PathSite R)) (j k : PathSite R) :
    cont (left ++ j :: (middle ++ k :: right)) * cont middle =
      cont (middle ++ k :: right) * cont (left ++ j :: middle) -
      cont right * (j.weight * edgeProduct middle * cont left) := by
  have h := first_wedge (left ++ [j]) (run middle (1, 0))
    (run middle (step k (run right (1, 0))))
  rw [wedge_run, last_edge] at h
  simp only [wedge, step, one_mul, mul_zero, sub_zero] at h
  simp only [cont, run_append, run, step] at h ⊢
  linear_combination h

/-- Matrix entry in zero-based natural indices. All entries outside the three
diagonals are zero. The finite matrix below only uses valid indices. -/
def entry : List (PathSite R) → Nat → Nat → R
  | [], _, _ => 0
  | a :: _, 0, 0 => a.diag
  | a :: _, 0, j + 1 => if j = 0 then a.upper else 0
  | a :: _, i + 1, 0 => if i = 0 then a.lower else 0
  | _ :: xs, i + 1, j + 1 => entry xs i j

def pathMatrix (xs : List (PathSite R)) : Matrix (Fin xs.length) (Fin xs.length) R :=
  fun i j => entry xs i.val j.val

private theorem det_corner {n : Nat} (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (row : ∀ j : Fin n, A 0 j.succ.succ = 0)
    (col : ∀ i : Fin n, A i.succ.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det -
      A 0 1 * A 1 0 *
        (A.submatrix (fun i : Fin n => i.succ.succ) (fun j : Fin n => j.succ.succ)).det := by
  classical
  let M := A.submatrix Fin.succ (1 : Fin (n + 2)).succAbove
  have mcol (i : Fin n) : M i.succ 0 = 0 := by
    simpa [M, Matrix.submatrix_apply, Fin.one_succAbove_zero] using col i
  have m00 : M 0 0 = A 1 0 := by
    simp [M, Matrix.submatrix_apply, Fin.one_succAbove_zero]
  have tail : M.submatrix Fin.succ Fin.succ =
      A.submatrix (fun i : Fin n => i.succ.succ) (fun j : Fin n => j.succ.succ) := by
    ext i j
    simp [M, Matrix.submatrix_apply, Fin.one_succAbove_succ]
  have md : M.det = A 1 0 *
      (A.submatrix (fun i : Fin n => i.succ.succ) (fun j : Fin n => j.succ.succ)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [mcol, m00, tail]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ, Nat.zero_add,
    pow_one, neg_one_mul, Fin.succ_zero_eq_one, Fin.val_one, row, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero]
  change _ + -(A 0 1) * M.det = _
  rw [md]
  ring

theorem det_cons_cons (a b : PathSite R) (xs : List (PathSite R)) :
    (pathMatrix (a :: b :: xs)).det =
      a.diag * (pathMatrix (b :: xs)).det - a.weight * (pathMatrix xs).det := by
  apply det_corner (n := xs.length)
  · intro j
    simp [pathMatrix, entry]
  · intro i
    simp [pathMatrix, entry]

/-- The recurrence computes the determinant of the actual tridiagonal
matrix over the coefficient ring, with arbitrary upper and lower entries. -/
theorem det_eq_cont (xs : List (PathSite R)) : (pathMatrix xs).det = cont xs := by
  match xs with
  | [] => simp [cont, run]
  | [a] =>
      rw [Matrix.det_fin_one, cont_singleton]
      rfl
  | a :: b :: rest =>
      rw [det_cons_cons, cont_cons_cons, det_eq_cont (b :: rest), det_eq_cont rest]
termination_by xs.length

/-- The two-cut identity stated directly for determinants of finite
tridiagonal matrices. Taking diagonal entries in a polynomial ring makes
this an identity of polynomials. -/
theorem det_condensation (left middle right : List (PathSite R)) (j k : PathSite R) :
    (pathMatrix (left ++ j :: (middle ++ k :: right))).det * (pathMatrix middle).det =
      (pathMatrix (middle ++ k :: right)).det * (pathMatrix (left ++ j :: middle)).det -
        (pathMatrix right).det * (j.weight * edgeProduct middle * (pathMatrix left).det) := by
  simpa only [det_eq_cont] using condensation left middle right j k

open Polynomial

/-- A physical site of the matrix (J), lifted to the entries of (sI-J). -/
noncomputable def pencilSite (a : PathSite R) : PathSite (Polynomial R) :=
  ⟨X - C a.diag, -C a.upper, -C a.lower⟩

@[simp] theorem pencil_weight (a : PathSite R) :
    (pencilSite a).weight = Polynomial.C a.weight := by
  simp [pencilSite, PathSite.weight]

@[simp] theorem pencil_edgeProduct (xs : List (PathSite R)) :
    edgeProduct (xs.map pencilSite) = Polynomial.C (edgeProduct xs) := by
  induction xs with
  | nil => simp [edgeProduct]
  | cons a xs ih =>
      change (pencilSite a).weight * edgeProduct (xs.map pencilSite) =
        Polynomial.C (a.weight * edgeProduct xs)
      rw [pencil_weight, ih, map_mul]

private theorem entry_pencil (xs : List (PathSite R)) (i j : Nat) (hi : i < xs.length) :
    entry (xs.map pencilSite) i j =
      (if i = j then X else 0) - C (entry xs i j) := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => simp [entry, pencilSite]
          | succ j => by_cases h : j = 0 <;> simp [entry, pencilSite, h]
      | succ i =>
          cases j with
          | zero => by_cases h : i = 0 <;> simp [entry, pencilSite, h]
          | succ j =>
              simpa only [List.map_cons, entry, Nat.succ.injEq] using
                ih i j (Nat.lt_of_succ_lt_succ hi)

/-- The continuant of the lifted data is the characteristic polynomial
as defined by mathlib for the actual finite tridiagonal matrix. -/
theorem charpoly_eq_cont (xs : List (PathSite R)) :
    (pathMatrix xs).charpoly = cont (xs.map pencilSite) := by
  let e : Fin xs.length ≃ Fin (xs.map pencilSite).length := finCongr (by simp)
  have he : (pathMatrix xs).charmatrix =
      (pathMatrix (xs.map pencilSite)).submatrix e e := by
    funext i j
    change (pathMatrix xs).charmatrix i j = entry (xs.map pencilSite) i.val j.val
    rw [entry_pencil xs i.val j.val i.isLt]
    by_cases hij : i = j
    · subst j
      simp [pathMatrix]
    · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp [Matrix.charmatrix_apply_ne _ _ _ hij, hval, pathMatrix]
  unfold Matrix.charpoly
  rw [he, Matrix.det_submatrix_equiv_self, det_eq_cont]

/-- The exact edge split for the spectral polynomials of a finite chain. -/
theorem charpoly_cut (left right : List (PathSite R)) (j k : PathSite R) :
    (pathMatrix (left ++ j :: k :: right)).charpoly =
      (pathMatrix (left ++ [j])).charpoly * (pathMatrix (k :: right)).charpoly -
      C j.weight * (pathMatrix left).charpoly * (pathMatrix right).charpoly := by
  simp only [charpoly_eq_cont, List.map_append, List.map_cons, List.map_nil]
  simpa only [pencil_weight] using
    cut (left.map pencilSite) (right.map pencilSite) (pencilSite j) (pencilSite k)

/-- The manuscript's (D B=W H-U P) for the characteristic polynomials
of subchains of a single tridiagonal matrix, with no nonsingularity,
genericity or positivity hypothesis. -/
theorem charpoly_condensation (left middle right : List (PathSite R)) (j k : PathSite R) :
    (pathMatrix (left ++ j :: (middle ++ k :: right))).charpoly * (pathMatrix middle).charpoly =
      (pathMatrix (middle ++ k :: right)).charpoly * (pathMatrix (left ++ j :: middle)).charpoly -
        (pathMatrix right).charpoly *
          (C (j.weight * edgeProduct middle) * (pathMatrix left).charpoly) := by
  simp only [charpoly_eq_cont, List.map_append, List.map_cons, map_mul]
  simpa only [pencil_weight, pencil_edgeProduct] using
    condensation (left.map pencilSite) (middle.map pencilSite) (right.map pencilSite)
      (pencilSite j) (pencilSite k)

end Continuant
end Catenary
