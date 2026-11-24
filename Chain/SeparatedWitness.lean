import Chain.SpectralPhysical
import Chain.MiddleRecovery

noncomputable section
open Polynomial Catenary.Continuant
open scoped Polynomial
namespace Catenary.SpectralPhysical

private theorem char_step (a b : PathSite ℝ) (xs : List (PathSite ℝ)) :
    intervalCharpoly (a::b::xs) = (X-C a.diag)*intervalCharpoly (b::xs) -
      C a.weight*intervalCharpoly xs := by
  simp only [intervalCharpoly,charpoly_eq_cont,List.map_cons,cont_cons_cons,pencil_weight]
  rfl

private theorem site_diag {m} (ℓ : Chamber m) (u : ℕ) (hu : u<m+1) :
    (physicalSite ℓ (rates ℓ) u).diag = (Spectral.site (u+1)).diag := by
  have h := actual_diagonal ℓ (⟨u,hu⟩ : Chamber m)
  simpa [physicalSite,hu,Spectral.site] using h

private theorem site_prod {m} (ℓ : Chamber m) (u : ℕ) (hu : u<m) :
    (physicalSite ℓ (rates ℓ) u).weight = 1 := by
  simpa [physicalSite,PathSite.weight,hu,mul_comm] using products ℓ ⟨u,hu⟩

/-- Every physical interval determinant agrees with the separated Jacobi
block on its original labels, at a single positive point for the specified leak. -/
theorem segment {m} (ℓ : Chamber m) (u q : ℕ) (h : u+q ≤ m+1) :
    intervalCharpoly (sitesFrom (physicalSite ℓ (rates ℓ)) u q) =
      Spectral.block (List.range' (u+1) q) := by
  induction q using Nat.strong_induction_on generalizing u with
  | h q ih =>
    cases q with
    | zero => exact (charpoly_eq_cont _).trans (by simp [sitesFrom])
    | succ q =>
      cases q with
      | zero =>
        have he := site_diag ℓ u (by omega)
        change intervalCharpoly [physicalSite ℓ (rates ℓ) u] = Spectral.block [u+1]
        rw [Spectral.block_one]
        exact (charpoly_eq_cont _).trans (by simp [pencilSite,he])
      | succ q =>
        let f := physicalSite ℓ (rates ℓ)
        have e₁ := ih (q+1) (by omega) (u+1) (by omega)
        have e₂ := ih q (by omega) (u+2) (by omega)
        change intervalCharpoly (f u :: f (u+1) :: sitesFrom f (u+2) q) =
          Spectral.block ((u+1)::(u+2)::List.range' (u+3) q)
        rw [char_step,Spectral.block_step,site_prod ℓ u (by omega),site_diag ℓ u (by omega)]
        change _ * intervalCharpoly (sitesFrom f (u+1) (q+1)) - C 1 * _ = _
        rw [e₁,e₂]
        simp [Spectral.site,List.range'_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem drop_sites {R : Type*} (f : ℕ → PathSite R) (u n k : ℕ) (h : k≤n) :
    (sitesFrom f u n).drop k = sitesFrom f (u+k) (n-k) := by
  induction k generalizing u n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [sitesFrom,List.drop_succ_cons,Nat.succ_sub_succ_eq_sub]
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (u+1) n (by omega)

theorem whole {m} (ℓ : Chamber m) :
    Middle.full ℓ (rates ℓ) = Spectral.block (List.range' 1 (m+1)) := segment ℓ 0 (m+1) (by omega)

theorem prefix_eq {m} (ℓ c : Chamber m) :
    Middle.prefix ℓ (rates ℓ) c.val = Spectral.block (List.range' 1 c.val) := by
  unfold Middle.prefix physicalSites
  rw [sitesFrom_take _ _ _ _ c.isLt.le]
  exact segment ℓ 0 c.val (by have := c.isLt; omega)

theorem suffix_eq {m} (ℓ c : Chamber m) :
    Middle.suffix ℓ (rates ℓ) c.val = Spectral.block (List.range' (c.val+2) (m-c.val)) := by
  unfold Middle.suffix physicalSites
  rw [drop_sites _ _ _ _ (by have := c.isLt; omega)]
  simpa using segment ℓ (c.val+1) (m-c.val) (by have := c.isLt; omega)

theorem disjoint_tags {m} (c : Chamber m) :
    (List.range' 1 c.val).Disjoint (List.range' (c.val+2) (m-c.val)) := by
  intro t hl hr
  rw [List.mem_range'_1] at hl hr
  omega

theorem split_tags {m} (c : Chamber m) :
    List.range' 1 (m+1) = List.range' 1 c.val ++ (c.val+1) :: List.range' (c.val+2) (m-c.val) := by
  have hh : (m+1) = c.val + ((m-c.val)+1) := by have := c.isLt; omega
  calc
    _ = List.range' 1 (c.val + ((m-c.val)+1)) := congrArg (fun n => List.range' 1 n) hh
    _ = List.range' 1 c.val ++ List.range' (1+c.val) ((m-c.val)+1) := List.range'_append_1.symm
    _ = _ := by simp [List.range'_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

private theorem full_root_suffix {left right : List ℕ} {j : ℕ} (hd : left.Disjoint right)
    {z : ℝ} (hz : (Spectral.block (left++j::right)).eval z=0) :
    (Spectral.block right).eval z ≠ 0 := by
  cases right with
  | nil => simp
  | cons b bs =>
    intro hr
    have htail := Spectral.adjacent_tail bs b z hr
    have hleft := Spectral.separated_real_roots (List.Disjoint.symm hd) hr
    rw [Spectral.cut] at hz
    have bad : (Spectral.block left).eval z * (Spectral.block bs).eval z = 0 := by
      simpa [hr] using hz
    exact mul_ne_zero hleft htail bad

theorem separated_branches {m} (ℓ c : Chamber m) :
    IsCoprime (Middle.prefix ℓ (rates ℓ) c.val) (Middle.suffix ℓ (rates ℓ) c.val) := by
  rw [prefix_eq,suffix_eq]
  exact Spectral.separated_coprime (List.nodup_range' (s:=1) (n:=c.val)) (disjoint_tags c)

/-- The entire denominator is coprime to the product of *any* proper
prefix and proper suffix appearing in a transfer numerator. -/
theorem no_cancellation {m} (ℓ u v : Chamber m) :
    IsCoprime (Middle.full ℓ (rates ℓ))
      (Middle.prefix ℓ (rates ℓ) u.val * Middle.suffix ℓ (rates ℓ) v.val) := by
  rw [whole,prefix_eq,suffix_eq]
  apply Spectral.coprime_of_distinct_zeros (List.nodup_range' (s:=1) (n:=m+1))
  intro z hz
  rw [eval_mul]
  exact mul_ne_zero (Spectral.full_root_prefix_ne (disjoint_tags u) ((split_tags u) ▸ hz))
    (full_root_suffix (disjoint_tags v) ((split_tags v) ▸ hz))

end Catenary.SpectralPhysical
