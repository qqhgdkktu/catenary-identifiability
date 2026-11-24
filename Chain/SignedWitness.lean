import Chain.ClosedChain

noncomputable section
open Polynomial Catenary.Continuant
open scoped Polynomial
namespace Catenary.Closed

def signedRates {m : ℕ} (L : ℕ → ℝ) (β : Fin m → ℝ) : Params m :=
  Gauge.pack (fun r => L (r.val+1)/L r.val)
    (fun r => β r/(L (r.val+1)/L r.val)) 0

@[simp] theorem signed_loss {m} (L : ℕ → ℝ) (β : Fin m → ℝ) :
    signedRates L β (loss m) = 0 := Gauge.pack_loss _ _ _

theorem signed_edges {m} (L : ℕ → ℝ) (β : Fin m → ℝ)
    (hL : ∀ t, t≤m → L t ≠ 0) (hβ : ∀ r, β r ≠ 0) (r : Fin m) :
    signedRates L β (fwd r) ≠ 0 ∧ signedRates L β (back r) ≠ 0 ∧
    signedRates L β (fwd r)*signedRates L β (back r) = β r := by
  have h := r.isLt
  have nz := div_ne_zero (hL (r.val+1) (by omega)) (hL r.val (by omega))
  simp only [signedRates,Gauge.pack_fwd,Gauge.pack_back]
  refine ⟨nz,div_ne_zero (hβ r) nz,?_⟩
  let y := L (r.val+1)/L r.val
  change y*(β r/y) = β r
  calc
    _ = β r*(y*y⁻¹) := by rw [div_eq_mul_inv]; ring
    _ = _ := by rw [mul_inv_cancel₀ nz,mul_one]

/-- Closed tridiagonal realization for arbitrary signed nonzero edge products.
The given L(t) are the leading determinants at the chosen spectral origin. -/
theorem signed_diagonal {m} (ℓ : Chamber m) (L d : ℕ → ℝ) (β : Fin m → ℝ)
    (hz : L 0=1) (hf : L 1=d 0) (hend : L (m+1)=0)
    (hn : ∀ t, t ≤ m → L t ≠ 0)
    (hstep : ∀ r : Fin m, L (r.val+2) = d (r.val+1)*L (r.val+1)-β r*L r.val)
    (c : Chamber m) : generator ℓ (signedRates L β) c c = -(d c.val) := by
  let a (r : Fin m) := L (r.val+1)/L r.val
  let b (r : Fin m) := β r/a r
  have he := Gauge.packed_diagonal ℓ c a b 0
  have af : (if ht : c.val<m then a ⟨c.val,ht⟩ else 0) = L (c.val+1)/L c.val := by
    split_ifs with h
    · rfl
    · have e : c.val=m := by have := c.isLt; omega
      simp [e,hend]
  rw [af] at he
  apply neg_eq_iff_eq_neg.mp
  change -(generator ℓ (Gauge.pack a b 0) c c) = _
  rw [he]
  simp only [ite_self,add_zero]
  obtain ⟨t,ht⟩ := c
  cases t with
  | zero => simp [hf,hz]
  | succ t =>
    have hr : t < m := by omega
    let r : Fin m := ⟨t,hr⟩
    have h₁ := hn (t+1) (by omega)
    have h₀ := hn t (by omega)
    have e := hstep r
    change L (t+2) = d (t+1)*L (t+1)-β r*L t at e
    simp only [Fin.val_mk,Nat.zero_lt_succ,dif_pos,Nat.add_sub_cancel] at *
    change L (t+2)/L (t+1) + β r/(L (t+1)/L t) = d (t+1)
    rw [e]
    field_simp

def spectralPrefix (z : ℝ) (t : ℕ) : ℝ := (Spectral.block (List.range' 1 t)).eval z

private theorem labels_sites (u q : ℕ) :
    sitesFrom (fun t => Spectral.site (t+1)) u q = (List.range' (u+1) q).map Spectral.site := by
  induction q generalizing u with
  | zero => rfl
  | succ q ih => simp [sitesFrom,List.range'_succ,ih,Nat.add_assoc]

theorem spectralPrefix_recurrence (z : ℝ) (t : ℕ) :
    spectralPrefix z (t+2) =
      (z+10*(((t+1:ℕ):ℝ)+1))*spectralPrefix z (t+1)-spectralPrefix z t := by
  have e := congrArg (Polynomial.eval z) (prefix_recurrence (fun u => Spectral.site (u+1)) t)
  simp only [labels_sites] at e
  simpa [spectralPrefix,Spectral.block,Spectral.site,PathSite.weight] using e

theorem prefix_nonzero {m} (z : ℝ) (hz : (Spectral.block (List.range' 1 (m+1))).eval z =0)
    (t : ℕ) (ht : t≤m) : spectralPrefix z t ≠ 0 := by
  let c : Chamber m := ⟨t,by omega⟩
  exact Spectral.full_root_prefix_ne (SpectralPhysical.disjoint_tags c)
    ((SpectralPhysical.split_tags c) ▸ hz)

def eigenRates (m : ℕ) (z : ℝ) : Params m := signedRates (spectralPrefix z) (fun _ : Fin m => 1)

/-- The algebraic spectral witness is realized with h=0. Such a signed
witness can certify a nonzero polynomial; positivity is obtained separately. -/
theorem eigen_witness {m} (ℓ : Chamber m) (z : ℝ)
    (hz : (Spectral.block (List.range' 1 (m+1))).eval z =0) :
    let θ := eigenRates m z
    θ (loss m)=0 ∧ (∀ c : Chamber m, generator ℓ θ c c = -(z+10*((c.val:ℝ)+1))) ∧
    ∀ r : Fin m, θ (fwd r) ≠ 0 ∧ θ (back r) ≠ 0 ∧ θ (fwd r)*θ (back r)=1 := by
  refine ⟨signed_loss _ _, ?_,?_⟩
  · intro c
    apply signed_diagonal ℓ (spectralPrefix z) (fun t => z+10*((t:ℝ)+1)) (fun _ => 1)
    · simp [spectralPrefix]
    · change (Spectral.block [1]).eval z = _
      simp [Spectral.block_one,Spectral.site]
    · exact hz
    · exact prefix_nonzero z hz
    · intro r
      simpa only [one_mul] using spectralPrefix_recurrence z r.val
  · exact signed_edges _ _ (prefix_nonzero z hz) (fun _ => one_ne_zero)

end Catenary.Closed
