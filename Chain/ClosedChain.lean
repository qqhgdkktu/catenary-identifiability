import Chain.SeparatedWitness
import Mathlib.Algebra.BigOperators.Intervals

/-! Evaluating the physical characteristic polynomial at zero, for arbitrary
real directed rates, including a zero leak and rates of either sign. -/
noncomputable section
open Polynomial Catenary.Continuant
open scoped Polynomial BigOperators
namespace Catenary.Closed

theorem sites_snoc {R : Type*} (f : ℕ → PathSite R) (u q : ℕ) :
    sitesFrom f u (q+1) = sitesFrom f u q ++ [f (u+q)] := by
  induction q generalizing u with
  | zero => simp [sitesFrom]
  | succ q ih =>
    change f u :: sitesFrom f (u+1) (q+1) = _
    rw [ih]
    simp [sitesFrom,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem prefix_recurrence {R : Type*} [CommRing R] (f : ℕ → PathSite R) (t : ℕ) :
    intervalCharpoly (sitesFrom f 0 (t+2)) =
      (X-C (f (t+1)).diag)*intervalCharpoly (sitesFrom f 0 (t+1)) -
      C (f t).weight*intervalCharpoly (sitesFrom f 0 t) := by
  have single (s : PathSite R) : intervalCharpoly [s] = X - C s.diag := by
    exact (charpoly_eq_cont _).trans (cont_singleton _)
  have empty : intervalCharpoly ([] : List (PathSite R)) = 1 :=
    (charpoly_eq_cont _).trans cont_nil
  have he := charpoly_cut (sitesFrom f 0 t) [] (f t) (f (t+1))
  rw [sites_snoc f 0 (t+1),sites_snoc f 0 t]
  simpa [single,empty,List.append_assoc,mul_comm] using he

def pref {m} (ℓ : Chamber m) (θ : Params m) (t : ℕ) :=
  (intervalCharpoly (sitesFrom (physicalSite ℓ θ) 0 t)).eval 0

private theorem phys_diag {m} (ℓ : Chamber m) (θ : Params m) (t : ℕ) (ht : t ≤ m) :
    -(physicalSite ℓ θ t).diag = PhysicalInverse.a θ t + PhysicalInverse.prev θ t +
      (if t = ℓ.val then θ (loss m) else 0) := by
  have h : t<m+1 := by omega
  simpa [physicalSite,h] using PhysicalInverse.diag_total ℓ (⟨t,h⟩ : Chamber m) θ

private theorem phys_weight {m} (ℓ : Chamber m) (θ : Params m) (t : ℕ) (ht : t < m) :
    (physicalSite ℓ θ t).weight = PhysicalInverse.a θ t * PhysicalInverse.b θ t := by
  simp [physicalSite,PathSite.weight,PhysicalInverse.a,PhysicalInverse.b,ht,mul_comm]

@[simp] theorem pref_zero {m} (ℓ : Chamber m) (θ : Params m) : pref ℓ θ 0 = 1 := by
  have z : intervalCharpoly ([] : List (PathSite ℝ)) = 1 := (charpoly_eq_cont _).trans cont_nil
  change (intervalCharpoly ([] : List (PathSite ℝ))).eval 0 = 1
  rw [z,eval_one]

private theorem pref_one {m} (ℓ : Chamber m) (θ : Params m) :
    pref ℓ θ 1 = PhysicalInverse.a θ 0 + (if 0=ℓ.val then θ (loss m) else 0) := by
  have h := phys_diag ℓ θ 0 (Nat.zero_le m)
  let u := physicalSite ℓ θ 0
  have z : intervalCharpoly [u] = X-C u.diag := (charpoly_eq_cont _).trans (cont_singleton _)
  change (intervalCharpoly [u]).eval 0 = _
  rw [z]
  simpa [u,PhysicalInverse.prev] using h

private theorem step {m} (ℓ : Chamber m) (θ : Params m) (t : ℕ) (ht : t<m) :
    pref ℓ θ (t+2)-PhysicalInverse.a θ (t+1)*pref ℓ θ (t+1) =
      PhysicalInverse.b θ t*(pref ℓ θ (t+1)-PhysicalInverse.a θ t*pref ℓ θ t)
      + (if t+1=ℓ.val then θ (loss m) else 0)*pref ℓ θ (t+1) := by
  have e := congrArg (Polynomial.eval (0:ℝ)) (prefix_recurrence (physicalSite ℓ θ) t)
  simp only [eval_sub,eval_mul,eval_X,eval_C,zero_sub,phys_diag ℓ θ (t+1) (by omega),
    phys_weight ℓ θ t ht,PhysicalInverse.prev] at e
  unfold pref
  linear_combination e

private def surplus {m} (ℓ : Chamber m) (θ : Params m) (t : ℕ) :=
  pref ℓ θ (t+1)-PhysicalInverse.a θ t*pref ℓ θ t

private theorem surplus_before {m} (ℓ : Chamber m) (θ : Params m) (t : ℕ) (ht : t<ℓ.val) :
    surplus ℓ θ t = 0 := by
  induction t with
  | zero => simp [surplus,pref_one,ne_of_lt ht]
  | succ t ih =>
    have e := step ℓ θ t (by have := ℓ.isLt; omega)
    change surplus ℓ θ (t+1) = PhysicalInverse.b θ t*surplus ℓ θ t + _ at e
    simpa [ih (by omega),ne_of_lt ht] using e

theorem pref_before {m} (ℓ : Chamber m) (θ : Params m) (t : ℕ) (ht : t≤ℓ.val) :
    pref ℓ θ t = ∏ r ∈ Finset.range t, PhysicalInverse.a θ r := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e := sub_eq_zero.mp (surplus_before ℓ θ t (by omega))
    rw [Finset.prod_range_succ,← ih (by omega), e, mul_comm]

/-- With a closed leak all proper leading minors at s=0 are exactly
the directed forward gains. This is an identity, including signed rates. -/
theorem prefix_closed {m} (ℓ : Chamber m) (θ : Params m) (hl : θ (loss m) = 0)
    (t : ℕ) (ht : t≤m+1) :
    pref ℓ θ t = ∏ r ∈ Finset.range t, PhysicalInverse.a θ r := by
  have zeros (u : ℕ) (hu : u≤m) : surplus ℓ θ u = 0 := by
    induction u with
    | zero => simp [surplus,pref_one,hl]
    | succ u ih =>
      have e := step ℓ θ u (by omega)
      change surplus ℓ θ (u+1) = PhysicalInverse.b θ u*surplus ℓ θ u + _ at e
      simpa [ih (by omega),hl] using e
  induction t with
  | zero => simp
  | succ t ih =>
    have e := sub_eq_zero.mp (zeros t (by omega))
    rw [Finset.prod_range_succ,← ih (by omega),e,mul_comm]

private theorem leak_surplus {m} (ℓ : Chamber m) (θ : Params m) :
    surplus ℓ θ ℓ.val = θ (loss m)*pref ℓ θ ℓ.val := by
  obtain ⟨p,hp⟩ := ℓ
  cases p with
  | zero => simp [surplus,pref_one]
  | succ p =>
    have he := step (⟨p+1,hp⟩ : Chamber m) θ p (by omega)
    have hz := surplus_before (⟨p+1,hp⟩ : Chamber m) θ p (by simp)
    change surplus _ _ (p+1) = PhysicalInverse.b θ p*surplus _ _ p + _ at he
    simpa [hz] using he

/-- Directed matrix tree formula with one leak on a path, for all real rates. -/
theorem determinant_at_zero {m} (ℓ : Chamber m) (θ : Params m) :
    pref ℓ θ (m+1) = θ (loss m) *
      (∏ r ∈ Finset.range ℓ.val, PhysicalInverse.a θ r) *
      (∏ d ∈ Finset.range (m-ℓ.val), PhysicalInverse.b θ (ℓ.val+d)) := by
  have along (d : ℕ) (hd : ℓ.val+d≤m) :
      surplus ℓ θ (ℓ.val+d) = θ (loss m)*pref ℓ θ ℓ.val *
        (∏ t ∈ Finset.range d, PhysicalInverse.b θ (ℓ.val+t)) := by
    induction d with
    | zero => simpa using leak_surplus ℓ θ
    | succ d ih =>
      have hne : ℓ.val+d+1 ≠ ℓ.val := by omega
      have e := step ℓ θ (ℓ.val+d) (by omega)
      change surplus _ _ (_+1) = PhysicalInverse.b θ _*surplus _ _ _ + _ at e
      simp only [hne,if_false,zero_mul,add_zero] at e
      rw [Finset.prod_range_succ]
      rw [ih (by omega)] at e
      change surplus _ _ (ℓ.val+d+1) = _
      rw [e]
      ring
  have he : ℓ.val+(m-ℓ.val)=m := by have := ℓ.isLt; omega
  have w := along (m-ℓ.val) (by omega)
  rw [he,surplus,pref_before ℓ θ ℓ.val le_rfl] at w
  simpa [PhysicalInverse.a] using w

end Catenary.Closed
