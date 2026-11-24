import Chain.ResolventGeneral
import Chain.ResolventPhysical
import Mathlib.Data.List.TakeDrop

/-! Transfer entries at arbitrary labelled chambers, with the original
positive physical parameters. -/
namespace Catenary
namespace Continuant

variable {K : Type*} [Field K]

theorem firstNumerator_take_drop (xs : List (PathSite K)) (v : Nat) (hv : v < xs.length) :
    firstNumerator xs v = directedProduct (xs.take v) * cont (xs.drop (v+1)) := by
  have h := firstNumerator_at_split (xs.take v) (xs.drop (v+1)) xs[v]
  have ht : (xs.take v).length = v := by simp [Nat.min_eq_left (Nat.le_of_lt hv)]
  rw [ht, ← List.drop_eq_getElem_cons hv, List.take_append_drop] at h
  exact h

/-- Uniform formula for both oriented entries for two ordered positions
on any nonsingular tridiagonal matrix with nonzero directed prefix edges. -/
theorem inv_at_indices (xs : List (PathSite K)) (i v : Fin xs.length) (hle : i ≤ v)
    (hD : cont xs ≠ 0) (hL : directedProduct (xs.take i.val) ≠ 0)
    (hU : directedProduct ((xs.take i.val).map swapSite) ≠ 0) :
    let l := cont (xs.take i.val)
    let t := xs.drop i.val
    let q := v.val - i.val
    (pathMatrix xs)⁻¹ v i = l * firstNumerator t q / cont xs ∧
    (pathMatrix xs)⁻¹ i v = l * firstNumerator (t.map swapSite) q / cont xs := by
  dsimp only
  obtain ⟨before, a, after_, heq, hb⟩ :
      ∃ (b : List (PathSite K)) (a : PathSite K) (t : List (PathSite K)),
        xs = b ++ a :: t ∧ b.length = i.val := by
    refine ⟨xs.take i.val, xs[i.val], xs.drop (i.val+1), ?_, ?_⟩
    · rw [← List.drop_eq_getElem_cons i.isLt, List.take_append_drop]
    · simp [Nat.min_eq_left i.isLt.le]
  subst xs
  have ht : (before ++ a :: after_).take i.val = before := by rw [← hb]; simp
  have hd : (before ++ a :: after_).drop i.val = a :: after_ := by rw [← hb]; simp
  rw [ht] at hL hU
  rw [ht, hd]
  have hv : v.val < before.length + (a :: after_).length := by simpa using v.isLt
  have hiv : i.val ≤ v.val := hle
  let w : Fin (a :: after_).length := ⟨v.val - i.val, by omega⟩
  have hs : (⟨before.length, by simp⟩ : Fin (before ++ a :: after_).length) = i := Fin.ext hb
  have hw : (⟨before.length+w.val, by
    rw [List.length_append]
    exact Nat.add_lt_add_left w.isLt _⟩ : Fin (before ++ a :: after_).length) = v :=
    Fin.ext (by dsimp [w]; omega)
  have lf := inv_from_input before a after_ w hD hL
  have rt := inv_to_left before a after_ w hD hU
  dsimp only at lf rt
  rw [hs, hw] at lf rt
  exact ⟨lf, rt⟩

omit [Field K] in
theorem sitesFrom_map {S : Type*} (g : PathSite K → PathSite S)
    (f : Nat → PathSite K) (s n : Nat) :
    (sitesFrom f s n).map g = sitesFrom (fun t => g (f t)) s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [sitesFrom, ih]

omit [Field K] in
theorem sitesFrom_take (f : Nat → PathSite K) (s n k : Nat) (h : k ≤ n) :
    (sitesFrom f s n).take k = sitesFrom f s k := by
  induction k generalizing s n with
  | zero => simp [sitesFrom]
  | succ k ih =>
      cases n with
      | zero => omega
      | succ n => simp [sitesFrom, ih (s+1) n (by omega)]

theorem directedProduct_ne_zero (f : Nat → PathSite K) (s n : Nat)
    (h : ∀ t, s ≤ t → t < s+n → (f t).lower ≠ 0) :
    directedProduct (sitesFrom f s n) ≠ 0 := by
  induction n generalizing s with
  | zero => simp [sitesFrom, directedProduct]
  | succ n ih =>
      change - (f s).lower * directedProduct (sitesFrom f (s+1) n) ≠ 0
      exact mul_ne_zero (neg_ne_zero.mpr (h s (by omega) (by omega)))
        (ih (s+1) (fun t h₁ h₂ => h t (by omega) (by omega)))

end Continuant
open Continuant

/-- Both transfer entries at a real value where the physical pencil
is nonsingular. The two products differ by the direction of their rates.
The outside factors are the prefix and suffix determinants. -/
theorem physical_transfer_formula {m : Nat} (ℓ i v : Chamber m) (θ : Params m) (s : ℝ)
    (hpos : Positive θ) (hiv : i ≤ v)
    (hD : (s • (1 : Mat m) - generator ℓ θ).det ≠ 0) :
    let sites := (physicalSites ℓ θ).map (shiftedSite s)
    let N := v.val - i.val
    let center := (sites.drop i.val).take N
    let l := cont (sites.take i.val)
    let r := cont (sites.drop (v.val+1))
    let D := cont sites
    (s • (1 : Mat m) - generator ℓ θ)⁻¹ v i = l * (directedProduct center * r) / D ∧
    (s • (1 : Mat m) - generator ℓ θ)⁻¹ i v =
      l * (directedProduct (center.map swapSite) * r) / D := by
  classical
  intro sites N center l r D
  let e : Chamber m ≃ Fin sites.length := finCongr (by simp [sites])
  have hM : s • (1 : Mat m) - generator ℓ θ = (pathMatrix sites).submatrix e e :=
    physical_pencil_eq_pathMatrix ℓ θ s
  have hdet : cont sites ≠ 0 := by
    rw [hM, Matrix.det_submatrix_equiv_self, det_eq_cont] at hD
    exact hD
  let f := fun t => shiftedSite s (physicalSite ℓ θ t)
  have hsites : sites = sitesFrom f 0 (m+1) := by
    unfold sites physicalSites f
    rw [sitesFrom_map]
  have htake : sites.take i.val = sitesFrom f 0 i.val := by
    rw [hsites, sitesFrom_take f 0 (m+1) i.val i.isLt.le]
  have hforward : directedProduct (sites.take i.val) ≠ 0 := by
    rw [htake]
    apply directedProduct_ne_zero
    intro t _ ht
    have hi := i.isLt
    let t' : Fin m := ⟨t, by omega⟩
    have h := physical_forward_factor ℓ θ s t'
    have hp := hpos (fwd t')
    change (shiftedSite s (physicalSite ℓ θ t)).lower ≠ 0
    change -(shiftedSite s (physicalSite ℓ θ t)).lower = _ at h
    linarith
  have hback : directedProduct ((sites.take i.val).map swapSite) ≠ 0 := by
    rw [htake, sitesFrom_map]
    apply directedProduct_ne_zero
    intro t _ ht
    have hi := i.isLt
    let t' : Fin m := ⟨t, by omega⟩
    have h := physical_backward_factor ℓ θ s t'
    have hp := hpos (back t')
    change (shiftedSite s (physicalSite ℓ θ t)).upper ≠ 0
    change -(shiftedSite s (physicalSite ℓ θ t)).upper = _ at h
    linarith
  have order : e i ≤ e v := hiv
  have h := inv_at_indices sites (e i) (e v) order hdet hforward hback
  dsimp only at h
  change (pathMatrix sites)⁻¹ (e v) (e i) =
      l * firstNumerator (sites.drop i.val) N / D ∧
    (pathMatrix sites)⁻¹ (e i) (e v) =
      l * firstNumerator ((sites.drop i.val).map swapSite) N / D at h
  have hlen : N < (sites.drop i.val).length := by
    have hi := i.isLt
    have hv := v.isLt
    have ile : i.val ≤ v.val := hiv
    simp only [List.length_drop, sites, List.length_map, physicalSites_length, N]
    omega
  have hlen' : N < ((sites.drop i.val).map swapSite).length := by simpa using hlen
  rw [firstNumerator_take_drop _ _ hlen, firstNumerator_take_drop _ _ hlen'] at h
  have off : i.val + (N+1) = v.val+1 := by
    have ile : i.val ≤ v.val := hiv
    dsimp [N]
    omega
  rw [physical_resolvent_entry ℓ θ s i v, physical_resolvent_entry ℓ θ s v i]
  simpa only [← List.map_take, ← List.map_drop, List.drop_drop, off, cont_swap, center, r] using h

end Catenary
