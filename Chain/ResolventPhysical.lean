import Chain.Continuant
import Chain.Model
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The physical generator has exactly the tridiagonal storage used by
the continuant proof. Labels in this file are zero-based. -/

namespace Catenary
namespace Continuant

variable {R : Type*} [CommRing R]

def sitesFrom (f : Nat → PathSite R) (start : Nat) : Nat → List (PathSite R)
  | 0 => []
  | n + 1 => f start :: sitesFrom f (start + 1) n

omit [CommRing R] in
@[simp] theorem sitesFrom_length (f : Nat → PathSite R) (start n : Nat) :
    (sitesFrom f start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [sitesFrom, ih]

theorem entry_sitesFrom (f : Nat → PathSite R) (start n i j : Nat)
    (hi : i < n) (hj : j < n) :
    entry (sitesFrom f start n) i j =
      if i = j then (f (start+i)).diag else
      if j = i+1 then (f (start+i)).upper else
      if i = j+1 then (f (start+j)).lower else 0 := by
  induction n generalizing start i j with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero =>
          cases j with
          | zero => simp [sitesFrom, entry]
          | succ j => simp [sitesFrom, entry]
      | succ i =>
          cases j with
          | zero => simp [sitesFrom, entry]
          | succ j =>
              simpa [sitesFrom, entry, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                ih (start+1) i j (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)

def shiftedSite (s : R) (a : PathSite R) : PathSite R :=
  ⟨s-a.diag, -a.upper, -a.lower⟩

theorem entry_shift (s : R) (xs : List (PathSite R)) (i j : Nat) (hi : i < xs.length) :
    entry (xs.map (shiftedSite s)) i j = (if i = j then s else 0) - entry xs i j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => simp [entry, shiftedSite]
          | succ j => by_cases h : j = 0 <;> simp [entry, shiftedSite, h]
      | succ i =>
          cases j with
          | zero => by_cases h : i = 0 <;> simp [entry, shiftedSite, h]
          | succ j =>
              simpa only [List.map_cons, entry, Nat.succ.injEq] using
                ih i j (Nat.lt_of_succ_lt_succ hi)

end Continuant

open Continuant

private theorem edge_offdiag {m : Nat} (src dst row col : Chamber m) (h : row ≠ col) :
    directedEdge src dst row col = if col = src ∧ row = dst then 1 else 0 := by
  by_cases hc : col = src
  · subst src
    simp [directedEdge, h]
  · simp [directedEdge, hc]

private theorem adjacent_distinct {m : Nat} (r : Fin m) : r.succ ≠ r.castSucc := by
  intro e
  have h := congrArg Fin.val e
  simp at h

private theorem backwards_impossible {m : Nat} (r t : Fin m) :
    ¬(r.castSucc = t.succ ∧ r.succ = t.castSucc) := by
  rintro ⟨h₁,h₂⟩
  have h₃ := congrArg Fin.val h₁
  have h₄ := congrArg Fin.val h₂
  simp only [Fin.coe_castSucc, Fin.val_succ] at h₃ h₄
  omega

theorem generator_lower {m : Nat} (ℓ : Chamber m) (θ : Params m) (r : Fin m) :
    generator ℓ θ r.succ r.castSucc = θ (fwd r) := by
  classical
  have hn := adjacent_distinct r
  have leak : ¬(r.succ = ℓ ∧ r.castSucc = ℓ) := fun h => hn (h.1.trans h.2.symm)
  have hf (t : Fin m) : (r.castSucc = t.castSucc ∧ r.succ = t.succ) ↔ t = r := by
    simp [eq_comm]
  simp [generator, edge_offdiag _ _ _ _ hn, hf, backwards_impossible r, leak, mul_ite]

theorem generator_upper {m : Nat} (ℓ : Chamber m) (θ : Params m) (r : Fin m) :
    generator ℓ θ r.castSucc r.succ = θ (back r) := by
  classical
  have hn := (adjacent_distinct r).symm
  have leak : ¬(r.castSucc = ℓ ∧ r.succ = ℓ) := fun h => hn (h.1.trans h.2.symm)
  have hb (t : Fin m) : (r.succ = t.succ ∧ r.castSucc = t.castSucc) ↔ t = r := by
    simp [eq_comm]
  have hf (t : Fin m) : ¬(r.succ = t.castSucc ∧ r.castSucc = t.succ) :=
    fun h => backwards_impossible r t ⟨h.2,h.1⟩
  simp [generator, edge_offdiag _ _ _ _ hn, hb, hf, leak, mul_ite]

theorem generator_offband {m : Nat} (ℓ row col : Chamber m) (θ : Params m)
    (h : row ≠ col) (hu : col.val ≠ row.val + 1) (hl : row.val ≠ col.val + 1) :
    generator ℓ θ row col = 0 := by
  have f (r : Fin m) : ¬(col = r.castSucc ∧ row = r.succ) := by
    rintro ⟨hc,hr⟩
    exact hl (by simp [hc,hr])
  have b (r : Fin m) : ¬(col = r.succ ∧ row = r.castSucc) := by
    rintro ⟨hc,hr⟩
    exact hu (by simp [hc,hr])
  have leak : ¬(row = ℓ ∧ col = ℓ) := fun e => h (e.1.trans e.2.symm)
  simp [generator, edge_offdiag _ _ _ _ h, f, b, leak]

/-- At vertex `t` the upper entry is its backwards rate and the lower
entry its forwards rate. The diagonal is taken from the specified generator. -/
noncomputable def physicalSite {m : Nat} (ℓ : Chamber m) (θ : Params m) (t : Nat) :
    PathSite ℝ where
  diag := if ht : t < m+1 then generator ℓ θ ⟨t,ht⟩ ⟨t,ht⟩ else 0
  upper := if ht : t < m then θ (back ⟨t,ht⟩) else 0
  lower := if ht : t < m then θ (fwd ⟨t,ht⟩) else 0

noncomputable def physicalSites {m : Nat} (ℓ : Chamber m) (θ : Params m) :
    List (PathSite ℝ) := sitesFrom (physicalSite ℓ θ) 0 (m+1)

theorem physical_forward_factor {m : Nat} (ℓ : Chamber m) (θ : Params m) (s : ℝ) (r : Fin m) :
    -(shiftedSite s (physicalSite ℓ θ r.val)).lower = θ (fwd r) := by
  simp [shiftedSite, physicalSite, r.isLt]

theorem physical_backward_factor {m : Nat} (ℓ : Chamber m) (θ : Params m) (s : ℝ) (r : Fin m) :
    -(shiftedSite s (physicalSite ℓ θ r.val)).upper = θ (back r) := by
  simp [shiftedSite, physicalSite, r.isLt]

theorem physical_edge_weight {m : Nat} (ℓ : Chamber m) (θ : Params m) (s : ℝ) (r : Fin m) :
    (shiftedSite s (physicalSite ℓ θ r.val)).weight = θ (fwd r) * θ (back r) := by
  simp [shiftedSite, physicalSite, PathSite.weight, r.isLt, mul_comm]

@[simp] theorem physicalSites_length {m : Nat} (ℓ : Chamber m) (θ : Params m) :
    (physicalSites ℓ θ).length = m+1 := by simp [physicalSites]

theorem physical_entry {m : Nat} (ℓ : Chamber m) (θ : Params m) (i j : Chamber m) :
    entry (physicalSites ℓ θ) i.val j.val = generator ℓ θ i j := by
  unfold physicalSites
  rw [entry_sitesFrom _ _ _ _ _ i.isLt j.isLt]
  simp only [Nat.zero_add]
  by_cases heq : i.val = j.val
  · have e : i = j := Fin.ext heq
    subst j
    simp [physicalSite, i.isLt]
  rw [if_neg heq]
  by_cases hu : j.val = i.val + 1
  · rw [if_pos hu]
    have hi : i.val < m := by omega
    let r : Fin m := ⟨i.val,hi⟩
    have h₁ : r.castSucc = i := rfl
    have h₂ : r.succ = j := Fin.ext hu.symm
    simpa [physicalSite, hi, r, h₁, h₂] using (generator_upper ℓ θ r).symm
  rw [if_neg hu]
  by_cases hl : i.val = j.val + 1
  · rw [if_pos hl]
    have hj : j.val < m := by omega
    let r : Fin m := ⟨j.val,hj⟩
    have h₁ : r.succ = i := Fin.ext hl.symm
    have h₂ : r.castSucc = j := rfl
    simpa [physicalSite, hj, r, h₁, h₂] using (generator_lower ℓ θ r).symm
  rw [if_neg hl]
  exact (generator_offband ℓ i j θ (fun h => heq (congrArg Fin.val h)) hu hl).symm

/-- The generator and the site-list matrix agree after the canonical
change between their definitionally presented finite index sets. -/
theorem generator_eq_pathMatrix {m : Nat} (ℓ : Chamber m) (θ : Params m) :
    generator ℓ θ = (pathMatrix (physicalSites ℓ θ)).submatrix
      (finCongr (physicalSites_length ℓ θ).symm) (finCongr (physicalSites_length ℓ θ).symm) := by
  funext i j
  exact (physical_entry ℓ θ i j).symm

theorem physical_charpoly_eq_cont {m : Nat} (ℓ : Chamber m) (θ : Params m) :
    (generator ℓ θ).charpoly = cont ((physicalSites ℓ θ).map pencilSite) := by
  rw [generator_eq_pathMatrix]
  let e := finCongr (physicalSites_length ℓ θ).symm
  change (Matrix.reindex e.symm e.symm (pathMatrix (physicalSites ℓ θ))).charpoly = _
  rw [Matrix.charpoly_reindex, charpoly_eq_cont]

/-- The resolvent pencil of the original physical parameters, at any
real spectral value, has the shifted site matrix used by the inverse formulas. -/
theorem physical_pencil_eq_pathMatrix {m : Nat} (ℓ : Chamber m) (θ : Params m) (s : ℝ) :
    let sites := (physicalSites ℓ θ).map (shiftedSite s)
    let e : Chamber m ≃ Fin sites.length := finCongr (by simp [sites])
    s • (1 : Mat m) - generator ℓ θ = (pathMatrix sites).submatrix e e := by
  intro sites e
  funext i j
  change (s • (1 : Mat m) - generator ℓ θ) i j =
      entry ((physicalSites ℓ θ).map (shiftedSite s)) i.val j.val
  rw [entry_shift _ _ _ _ (by simp), physical_entry]
  by_cases h : i = j
  · subst j
    simp [Matrix.smul_apply]
  · have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [Matrix.smul_apply, Matrix.one_apply, h, hv]

theorem physical_resolvent_entry {m : Nat} (ℓ : Chamber m) (θ : Params m) (s : ℝ)
    (input output : Chamber m) :
    let sites := (physicalSites ℓ θ).map (shiftedSite s)
    let e : Chamber m ≃ Fin sites.length := finCongr (by simp [sites])
    (s • (1 : Mat m) - generator ℓ θ)⁻¹ output input =
      (pathMatrix sites)⁻¹ (e output) (e input) := by
  intro sites e
  have eqn : s • (1 : Mat m) - generator ℓ θ = Matrix.reindex e.symm e.symm (pathMatrix sites) :=
    physical_pencil_eq_pathMatrix ℓ θ s
  rw [eqn, Matrix.inv_reindex]
  rfl

end Catenary
