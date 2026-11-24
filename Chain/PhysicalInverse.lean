import Chain.ResolventPhysical
import Mathlib.Tactic.Linarith

noncomputable section
open scoped BigOperators
namespace Catenary
namespace PhysicalInverse

def a {m} (θ : Params m) (t : ℕ) : ℝ :=
  if ht : t < m then θ (fwd ⟨t,ht⟩) else 0
def b {m} (θ : Params m) (t : ℕ) : ℝ :=
  if ht : t < m then θ (back ⟨t,ht⟩) else 0
def prev {m} (θ : Params m) : ℕ → ℝ
  | 0 => 0
  | t+1 => b θ t

private theorem edge_self {m} (src dst col : Chamber m) (hne : src ≠ dst) :
    directedEdge src dst col col = if col = src then -1 else 0 := by
  by_cases h : col = src
  · subst col
    simp [directedEdge,hne]
  · simp [directedEdge,h]

private theorem forward_sum {m} (θ : Params m) (col : Chamber m) :
    (∑ r : Fin m, if col = r.castSucc then θ (fwd r) else 0) = a θ col.val := by
  by_cases ht : col.val < m
  · let r : Fin m := ⟨col.val,ht⟩
    have he (t : Fin m) : col = t.castSucc ↔ t = r := by
      simp [Fin.ext_iff,r,eq_comm]
    simp [he,a,ht,r]
  · have hh (t : Fin m) : col ≠ t.castSucc := by
      intro h
      apply ht
      rw [h]
      exact t.isLt
    simp [hh,a,ht]

private theorem backward_sum {m} (θ : Params m) (col : Chamber m) :
    (∑ r : Fin m, if col = r.succ then θ (back r) else 0) = prev θ col.val := by
  obtain ⟨t,ht⟩ := col
  cases t with
  | zero =>
    have hh (r : Fin m) : (⟨0,ht⟩ : Chamber m) ≠ r.succ := by
      simp [Fin.ext_iff]
    simp only [if_neg (hh _),Finset.sum_const_zero,prev]
  | succ t =>
    have hh : t < m := by omega
    let r : Fin m := ⟨t,hh⟩
    have he (s : Fin m) : (⟨t+1,ht⟩ : Chamber m) = s.succ ↔ s = r := by
      simp [Fin.ext_iff,r,eq_comm]
    simp [he,b,prev,hh,r]

theorem diag_total {m} (ℓ col : Chamber m) (θ : Params m) :
    -(generator ℓ θ col col) =
      a θ col.val + prev θ col.val + (if col.val = ℓ.val then θ (loss m) else 0) := by
  have hne (r : Fin m) : r.castSucc ≠ r.succ := by simp [Fin.ext_iff]
  have e (r : Fin m) : (θ (fwd r) * directedEdge r.castSucc r.succ col col +
      θ (back r) * directedEdge r.succ r.castSucc col col) =
      - ((if col = r.castSucc then θ (fwd r) else 0) +
         (if col = r.succ then θ (back r) else 0)) := by
    rw [edge_self _ _ _ (hne r),edge_self _ _ _ (hne r).symm]
    split_ifs <;> ring
  simp only [generator,e,Finset.sum_neg_distrib,Finset.sum_add_distrib,forward_sum,backward_sum,
    and_self]
  simp only [Fin.ext_iff]
  ring

/-- With one known leak, the diagonal entries and all adjacent products
determine every physical rate globally on the entire positive orthant. -/
theorem signed_rates_of_diagonal_and_products {m} (ℓ : Chamber m) (θ η : Params m)
    (hθ : ∀ r : Fin m, θ (back r) ≠ 0) (hη : ∀ r : Fin m, η (fwd r) ≠ 0)
    (hdiag : ∀ c, generator ℓ θ c c = generator ℓ η c c)
    (hprod : ∀ r : Fin m, θ (fwd r)*θ (back r) = η (fwd r)*η (back r)) : θ = η := by
  have total (t : ℕ) (ht : t ≤ m) :
      a θ t + prev θ t + (if t = ℓ.val then θ (loss m) else 0) =
      a η t + prev η t + (if t = ℓ.val then η (loss m) else 0) := by
    let c : Chamber m := ⟨t,by omega⟩
    exact (diag_total ℓ c θ).symm.trans ((congrArg Neg.neg (hdiag c)).trans (diag_total ℓ c η))
  have prod (t : ℕ) (ht : t < m) : a θ t * b θ t = a η t * b η t := by
    simpa [a,b,ht] using hprod ⟨t,ht⟩
  have eqB (t : ℕ) (ht : t<m) (ha : a θ t = a η t) : b θ t = b η t := by
    have h := prod t ht
    rw [ha] at h
    have hn : a η t ≠ 0 := by simpa [a,ht] using hη ⟨t,ht⟩
    exact mul_left_cancel₀ hn h
  have eqA (t : ℕ) (ht : t<m) (hb : b θ t = b η t) : a θ t = a η t := by
    have h := prod t ht
    rw [← hb] at h
    have hn : b θ t ≠ 0 := by simpa [b,ht] using hθ ⟨t,ht⟩
    exact mul_right_cancel₀ hn h
  have left (t : ℕ) : t < ℓ.val → a θ t = a η t ∧ b θ t = b η t := by
    induction t with
    | zero =>
      intro h
      have hbound := ℓ.isLt
      have hh : a θ 0 = a η 0 := by simpa [prev,ne_of_lt h] using total 0 (Nat.zero_le m)
      exact ⟨hh,eqB _ (by omega) hh⟩
    | succ t ih =>
      intro h
      have hbound := ℓ.isLt
      have hp := (ih (by omega)).2
      have hh : a θ (t+1) = a η (t+1) := by
        have e := total (t+1) (by omega)
        simpa [prev,ne_of_lt h,hp] using e
      exact ⟨hh,eqB _ (by omega) hh⟩
  have right (d : ℕ) : ∀ t : ℕ, t < m → ℓ.val ≤ t → t+d=m →
      a θ t = a η t ∧ b θ t = b η t := by
    induction d with
    | zero => intro t ht _ e; omega
    | succ d ih =>
      intro t ht hℓ he
      have ha : a θ (t+1) = a η (t+1) := by
        by_cases hn : t+1 < m
        · exact (ih (t+1) hn (by omega) (by omega)).1
        · simp [a,hn]
      have hb : b θ t = b η t := by
        have e := total (t+1) (by omega)
        have hn : t+1 ≠ ℓ.val := by omega
        simpa [prev,hn,ha] using e
      exact ⟨eqA _ ht hb,hb⟩
  have edges (t : ℕ) (ht : t < m) : a θ t = a η t ∧ b θ t = b η t := by
    by_cases h : t < ℓ.val
    · exact left t h
    · exact right (m-t) t ht (by omega) (by omega)
  have af (t : ℕ) : a θ t = a η t := by
    by_cases ht : t<m
    · exact (edges t ht).1
    · simp [a,ht]
  have bf (t : ℕ) : b θ t = b η t := by
    by_cases ht : t<m
    · exact (edges t ht).2
    · simp [b,ht]
  have pf (t : ℕ) : prev θ t = prev η t := by cases t with
    | zero => rfl
    | succ t => exact bf t
  have hloss : θ (loss m) = η (loss m) := by
    simpa [af,pf] using total ℓ.val (Nat.le_of_lt_succ ℓ.isLt)
  funext q
  by_cases h1 : q.val < m
  · let r : Fin m := ⟨q.val,h1⟩
    have eq : fwd r = q := Fin.ext rfl
    rw [← eq]
    simpa [a,r.isLt] using af r.val
  · by_cases h2 : q.val < 2*m
    · let r : Fin m := ⟨q.val-m,by omega⟩
      have eq : back r = q := Fin.ext (by dsimp [back,r]; omega)
      rw [← eq]
      simpa [b,r.isLt] using bf r.val
    · have eq : loss m = q := Fin.ext (by have := q.isLt; dsimp [loss]; omega)
      simpa [eq] using hloss

theorem rates_of_diagonal_and_products {m} (ℓ : Chamber m) (θ η : Params m)
    (hθ : Positive θ) (hη : Positive η)
    (hdiag : ∀ c, generator ℓ θ c c = generator ℓ η c c)
    (hprod : ∀ r : Fin m, θ (fwd r)*θ (back r) = η (fwd r)*η (back r)) : θ = η :=
  signed_rates_of_diagonal_and_products ℓ θ η (fun r => (hθ (back r)).ne') (fun r => (hη (fwd r)).ne') hdiag hprod

end PhysicalInverse
end Catenary
