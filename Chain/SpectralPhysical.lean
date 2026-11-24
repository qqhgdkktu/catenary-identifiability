import Chain.GaugePhysical
import Chain.Spectral

/-! An explicit positive physical realization of the unit-edge separated
spectrum for *every* leak chamber. The recursions start at both endpoints. -/
noncomputable section
open Polynomial Catenary.Continuant
open scoped Polynomial
namespace Catenary.SpectralPhysical

private def diagonal (t : ℕ) : ℝ := 10*((t:ℝ)+1)
private theorem diagonal_large (t : ℕ) : 3 ≤ diagonal t := by
  unfold diagonal
  have h : (0:ℝ) ≤ t := Nat.cast_nonneg t
  linarith
private def runPivot (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => d 0
  | t+1 => d (t+1) - (runPivot d t)⁻¹

private theorem pivot_two (d : ℕ → ℝ) (hd : ∀ t, 3 ≤ d t) (t : ℕ) : 2 ≤ runPivot d t := by
  induction t with
  | zero => exact le_trans (by norm_num) (hd 0)
  | succ t ih =>
    have hh : (runPivot d t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h := hd (t+1)
    change 2 ≤ d (t+1) - _
    linarith

private def f (t : ℕ) := runPivot diagonal t
private def g (m t : ℕ) := runPivot (fun r => diagonal (m-r)) t
private theorem f_large (t) : 2 ≤ f t := pivot_two _ diagonal_large _
private theorem g_large (m t) : 2 ≤ g m t := pivot_two _ (fun u => diagonal_large (m-u)) _

private def A {m} (ℓ : Chamber m) (r : Fin m) : ℝ :=
  if r.val < ℓ.val then f r.val else (g m (m-(r.val+1)))⁻¹
private def B {m} (ℓ : Chamber m) (r : Fin m) : ℝ :=
  if r.val < ℓ.val then (f r.val)⁻¹ else g m (m-(r.val+1))
private def outgoingA {m} (ℓ c : Chamber m) : ℝ :=
  if ht : c.val < m then A ℓ ⟨c.val,ht⟩ else 0
private def outgoingB {m} (ℓ c : Chamber m) : ℝ :=
  if ht : 0 < c.val then B ℓ ⟨c.val-1,by have := c.isLt; omega⟩ else 0
private def lossRate {m} (ℓ : Chamber m) :=
  diagonal ℓ.val - outgoingA ℓ ℓ - outgoingB ℓ ℓ

def rates {m} (ℓ : Chamber m) : Params m := Gauge.pack (A ℓ) (B ℓ) (lossRate ℓ)

private theorem loss_pos {m} (ℓ : Chamber m) : 0 < lossRate ℓ := by
  have h₁ : outgoingA ℓ ℓ ≤ 1 := by
    unfold outgoingA
    split_ifs with h
    · simp only [A,lt_irrefl,if_false]
      exact inv_le_one_of_one_le₀ (le_trans (by norm_num) (g_large _ _))
    · norm_num
  have h₂ : outgoingB ℓ ℓ ≤ 1 := by
    unfold outgoingB
    split_ifs with h
    · simp only [B,show ℓ.val - 1 < ℓ.val by omega,if_true]
      exact inv_le_one_of_one_le₀ (le_trans (by norm_num) (f_large _))
    · norm_num
  have hd := diagonal_large ℓ.val
  unfold lossRate
  linarith

theorem positive {m} (ℓ : Chamber m) : Positive (rates ℓ) := by
  intro r
  unfold rates Gauge.pack A B
  split_ifs
  all_goals try apply inv_pos.mpr
  all_goals first
    | exact loss_pos ℓ
    | exact lt_of_lt_of_le (by norm_num) (f_large _)
    | exact lt_of_lt_of_le (by norm_num) (g_large _ _)

theorem products {m} (ℓ : Chamber m) (r : Fin m) :
    rates ℓ (fwd r) * rates ℓ (back r) = 1 := by
  simp only [rates,Gauge.pack_fwd,Gauge.pack_back,A,B]
  split_ifs with h
  · exact mul_inv_cancel₀ (by have := f_large r.val; linarith)
  · exact inv_mul_cancel₀ (by have := g_large m (m-(r.val+1)); linarith)

private theorem outgoing {m} (ℓ c : Chamber m) :
    outgoingA ℓ c + outgoingB ℓ c + (if c.val=ℓ.val then lossRate ℓ else 0) = diagonal c.val := by
  by_cases eq : c.val = ℓ.val
  · have h : c = ℓ := Fin.ext eq
    subst c
    simp [lossRate]
  by_cases left : c.val < ℓ.val
  · have ht : c.val < m := by have := ℓ.isLt; omega
    cases c with
    | mk t h =>
      cases t with
      | zero =>
        simp [outgoingA,outgoingB,A,ht,left,eq,f,runPivot]
      | succ t =>
        change t+1 < ℓ.val at left
        have hlt : t<ℓ.val := by omega
        simp [outgoingA,outgoingB,A,B,ht,left,hlt,eq,f,runPivot]
  · have ht := c.isLt
    have right : ℓ.val < c.val := by omega
    have hpred : ¬ c.val-1 < ℓ.val := by omega
    have hpos : 0 < c.val := by omega
    have hpred' : c.val-1+1 = c.val := by omega
    by_cases bound : c.val < m
    · have hind : m-c.val = (m-(c.val+1))+1 := by omega
      have mind : m-((m-(c.val+1))+1) = c.val := by omega
      have hrec : g m (m-c.val) = diagonal c.val - (g m (m-(c.val+1)))⁻¹ := by
        rw [hind]
        exact (by simp [g,runPivot,mind])
      simp [outgoingA,outgoingB,A,B,bound,hpos,left,hpred,hpred',eq,hrec]
    · have hcm : c.val = m := by omega
      have hg0 : g m (m-c.val) = diagonal c.val := by simp [hcm,g,runPivot]
      simp [outgoingA,outgoingB,A,B,bound,hpos,left,hpred,hpred',eq,hg0]

theorem actual_diagonal {m} (ℓ c : Chamber m) :
    generator ℓ (rates ℓ) c c = -(10*((c.val:ℝ)+1)) := by
  have h := Gauge.packed_diagonal ℓ c (A ℓ) (B ℓ) (lossRate ℓ)
  change -(generator ℓ (rates ℓ) c c) =
    outgoingA ℓ c + outgoingB ℓ c + (if c.val=ℓ.val then lossRate ℓ else 0) at h
  exact neg_eq_iff_eq_neg.mp (h.trans (outgoing ℓ c))

end Catenary.SpectralPhysical
