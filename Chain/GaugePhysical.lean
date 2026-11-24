import Chain.Gauge
import Chain.ResolventPhysical
import Chain.Obstruction
import Chain.PhysicalInverse

noncomputable section
open scoped BigOperators Matrix
namespace Catenary.Gauge

def pack {m} (a b : Fin m → ℝ) (h : ℝ) (t : Fin (2*m+1)) : ℝ :=
  if h₁ : t.val < m then a ⟨t.val,h₁⟩
  else if h₂ : t.val < 2*m then b ⟨t.val-m,by omega⟩ else h

@[simp] theorem pack_fwd {m} (a b : Fin m → ℝ) (h : ℝ) (r : Fin m) :
    pack a b h (fwd r) = a r := by simp [pack,fwd,r.isLt]

@[simp] theorem pack_back {m} (a b : Fin m → ℝ) (h : ℝ) (r : Fin m) :
    pack a b h (back r) = b r := by
  have hr := r.isLt
  have h₁ : ¬m+r.val < m := by omega
  have h₂ : m+r.val < 2*m := by omega
  simp [pack,back,h₁,h₂]

@[simp] theorem pack_loss {m} (a b : Fin m → ℝ) (h : ℝ) :
    pack a b h (loss m) = h := by
  simp [pack,loss,show ¬ 2*m < m by omega]

theorem packed_diagonal {m} (ℓ c : Chamber m) (a b : Fin m → ℝ) (h : ℝ) :
    -(generator ℓ (pack a b h) c c) =
      (if ht : c.val < m then a ⟨c.val,ht⟩ else 0) +
      (if ht : 0 < c.val then b ⟨c.val-1,by have := c.isLt; omega⟩ else 0) +
      (if c.val = ℓ.val then h else 0) := by
  rw [PhysicalInverse.diag_total]
  cases c with
  | mk t ht =>
    cases t with
    | zero => simp [PhysicalInverse.a,PhysicalInverse.b,PhysicalInverse.prev]
    | succ t => simp [PhysicalInverse.a,PhysicalInverse.b,PhysicalInverse.prev,show t<m by omega]

def Band {m} (J : Mat m) : Prop :=
  ∀ a b : Chamber m, a ≠ b → b.val ≠ a.val+1 → a.val ≠ b.val+1 → J a b = 0

def extract {m} (G : Mat m) (h : ℝ) : Params m :=
  pack (fun r => G r.succ r.castSucc) (fun r => G r.castSucc r.succ) h

theorem generator_extract {m} (G : Mat m) (h : ℝ) (ℓ : Chamber m) (hband : Band G)
    (hbal : ∀ c, ∑ r, G r c = -(if c = ℓ then h else 0)) :
    generator ℓ (extract G h) = G := by
  let θ := extract G h
  have off (r c : Chamber m) (hr : r ≠ c) : generator ℓ θ r c = G r c := by
    by_cases h₁ : c.val = r.val+1
    · let t : Fin m := ⟨r.val,by have := c.isLt; omega⟩
      have ha : t.castSucc = r := Fin.ext rfl
      have hb : t.succ = c := Fin.ext h₁.symm
      rw [← ha,← hb,generator_upper]
      simp [θ,extract]
    by_cases h₂ : r.val = c.val+1
    · let t : Fin m := ⟨c.val,by have := r.isLt; omega⟩
      have ha : t.castSucc = c := Fin.ext rfl
      have hb : t.succ = r := Fin.ext h₂.symm
      rw [← ha,← hb,generator_lower]
      simp [θ,extract]
    exact (generator_offband ℓ r c θ hr h₁ h₂).trans (hband r c hr h₁ h₂).symm
  ext r c
  by_cases eq : r=c
  · subst r
    have d (u : Chamber m) : generator ℓ θ u c-G u c =
        if u=c then generator ℓ θ c c - G c c else 0 := by
      by_cases he : u=c <;> simp [he, off, *]
    have hsum : (∑ u, (generator ℓ θ u c-G u c)) = 0 := by
      simp [Finset.sum_sub_distrib, generator_columnSum,hbal,θ,extract]
    have splitSum : (∑ u, (generator ℓ θ u c - G u c)) = generator ℓ θ c c - G c c := by
      calc
        _ = ∑ u : Chamber m, if u=c then generator ℓ θ c c - G c c else 0 :=
          Finset.sum_congr rfl (fun u _ => d u)
        _ = _ := by simp
    exact sub_eq_zero.mp (splitSum.symm.trans hsum)
  · exact off r c eq

/-- Give all 2m+1 original rates explicitly and recover exactly the
diagonally scaled Jacobi matrix with the single specified leak. -/
theorem realize {m} (J : Mat m) (w : Chamber m → ℝ) (ℓ : Chamber m)
    (hs : J.IsSymm) (hb : Band J) (he : ∀ r : Fin m, 0 < J r.succ r.castSucc)
    (hw : ∀ c, 0 < w c) (hJ : (-J).mulVec w = Pi.single ℓ 1) :
    let θ := extract (scaled w J) (1/w ℓ)
    Positive θ ∧ generator ℓ θ = scaled w J := by
  dsimp only
  constructor
  · intro t
    unfold extract pack
    split_ifs with h₁ h₂
    · exact div_pos (mul_pos (hw _) (he _)) (hw _)
    · let r : Fin m := ⟨t.val-m,by omega⟩
      have hl : 0 < J r.castSucc r.succ := (hs.apply r.succ r.castSucc) ▸ he r
      exact div_pos (mul_pos (hw _) hl) (hw _)
    · exact one_div_pos.mpr (hw _)
  · apply generator_extract
    · intro a b h h₁ h₂
      simp [scaled,hb a b h h₁ h₂]
    · exact column_balance ℓ hs hJ

end Catenary.Gauge
