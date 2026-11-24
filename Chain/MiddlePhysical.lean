import Chain.Middle
import Chain.PhysicalInverse
import Chain.ResolventFormula

/-! Actual physical parameters, encoded in the two branches pointing away from
an interior input. The labels in the path lists are zero-based. -/

noncomputable section

open Polynomial Catenary.Continuant
open scoped Polynomial

namespace Catenary.Middle

variable {K : Type*} [CommRing K]

def rightCode (d : ℕ → K) (w : ℕ → Kˣ) (u : ℕ) : (q : ℕ) → JacobiData K q
  | 0 => .single (d u)
  | q+1 => .extend (d u) (w u) (rightCode d w (u+1) q)

def leftCode (d : ℕ → K) (w : ℕ → Kˣ) (u : ℕ) : (q : ℕ) → JacobiData K q
  | 0 => .single (d u)
  | q+1 => .extend (d (u+q+1)) (w (u+q)) (leftCode d w u q)

omit [CommRing K] in
theorem from_append (f : ℕ → PathSite K) (u a b : ℕ) :
    sitesFrom f u (a+b) = sitesFrom f u a ++ sitesFrom f (u+a) b := by
  induction a generalizing u with
  | zero => simp [sitesFrom]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [sitesFrom, List.cons_append, ih]
    congr 3
    omega

private theorem char_one (u : PathSite K) : intervalCharpoly [u] = X - C u.diag :=
  (charpoly_eq_cont _).trans (cont_singleton _)

private theorem char_none : intervalCharpoly ([] : List (PathSite K)) = 1 :=
  (charpoly_eq_cont _).trans cont_nil

private theorem head_eq (u v : PathSite K) (xs : List (PathSite K)) :
    intervalCharpoly (u :: v :: xs) = (X - C u.diag) * intervalCharpoly (v :: xs) -
      C u.weight * intervalCharpoly xs := by
  have h := charpoly_cut [] xs u v
  change intervalCharpoly (u :: v :: xs) = intervalCharpoly [u] * intervalCharpoly (v :: xs) -
      C u.weight * intervalCharpoly [] * intervalCharpoly xs at h
  simpa [char_one, char_none] using h

private theorem end_eq (xs : List (PathSite K)) (u v : PathSite K) :
    intervalCharpoly (xs ++ [u,v]) = (X - C v.diag) * intervalCharpoly (xs ++ [u]) -
      C u.weight * intervalCharpoly xs := by
  have h := charpoly_cut xs [] u v
  change intervalCharpoly (xs ++ [u,v]) = intervalCharpoly (xs ++ [u]) * intervalCharpoly [v] -
      C u.weight * intervalCharpoly xs * intervalCharpoly [] at h
  simpa only [char_one, char_none, mul_one, one_mul, mul_comm] using h

theorem right_pair (f : ℕ → PathSite K) (w : ℕ → Kˣ) (u q : ℕ)
    (hw : ∀ t, u ≤ t → t < u+q → (w t : K) = (f t).weight) :
    (rightCode (fun t => (f t).diag) w u q).boundaryPair =
      (intervalCharpoly (sitesFrom f u (q+1)), intervalCharpoly (sitesFrom f (u+1) q)) := by
  induction q generalizing u with
  | zero =>
    exact Prod.ext ((JacobiData.boundaryPair_single _).trans (char_one _).symm) rfl
  | succ q ih =>
    have e := ih (u+1) (fun t h₁ h₂ => hw t (by omega) (by omega))
    apply Prod.ext
    · change (JacobiData.extend _ _ _).boundaryPair.1 = _
      rw [JacobiData.boundaryPair_extend, e]
      simp only [hw u (le_refl _) (by omega)]
      exact (head_eq _ _ _).symm
    · exact congrArg Prod.fst e

theorem left_pair (f : ℕ → PathSite K) (w : ℕ → Kˣ) (u q : ℕ)
    (hw : ∀ t, u ≤ t → t < u+q → (w t : K) = (f t).weight) :
    (leftCode (fun t => (f t).diag) w u q).boundaryPair =
      (intervalCharpoly (sitesFrom f u (q+1)), intervalCharpoly (sitesFrom f u q)) := by
  induction q with
  | zero =>
    exact Prod.ext ((JacobiData.boundaryPair_single _).trans (char_one _).symm) rfl
  | succ q ih =>
    have e := ih (fun t h₁ h₂ => hw t h₁ (by omega))
    apply Prod.ext
    · change (JacobiData.extend _ _ _).boundaryPair.1 = _
      rw [JacobiData.boundaryPair_extend, e]
      simp only [hw (u+q) (by omega) (by omega)]
      rw [from_append f u q 2, from_append f u q 1]
      exact (end_eq _ _ _).symm
    · exact congrArg Prod.fst e

theorem right_inj (d e : ℕ → K) (v w : ℕ → Kˣ) (u q : ℕ)
    (h : rightCode d v u q = rightCode e w u q) :
    (∀ t, t ≤ q → d (u+t) = e (u+t)) ∧ (∀ t, t < q → v (u+t) = w (u+t)) := by
  induction q generalizing u with
  | zero =>
    have he := JacobiData.single.inj h
    simp_all
  | succ q ih =>
    obtain ⟨hd, hw, htail⟩ := JacobiData.extend.inj h
    obtain ⟨h₁,h₂⟩ := ih (u+1) htail
    constructor
    · intro t ht
      cases t with
      | zero => exact hd
      | succ t => simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h₁ t (by omega)
    · intro t ht
      cases t with
      | zero => exact hw
      | succ t => simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h₂ t (by omega)

theorem left_inj (d e : ℕ → K) (v w : ℕ → Kˣ) (u q : ℕ)
    (h : leftCode d v u q = leftCode e w u q) :
    (∀ t, t ≤ q → d (u+t) = e (u+t)) ∧ (∀ t, t < q → v (u+t) = w (u+t)) := by
  induction q with
  | zero =>
    have he := JacobiData.single.inj h
    simp_all
  | succ q ih =>
    obtain ⟨hd, hw, htail⟩ := JacobiData.extend.inj h
    obtain ⟨h₁,h₂⟩ := ih htail
    constructor
    · intro t ht
      by_cases hq : t ≤ q
      · exact h₁ t hq
      · have e : t = q+1 := by omega
        simpa [e, Nat.add_assoc] using hd
    · intro t ht
      by_cases hq : t < q
      · exact h₂ t hq
      · have e : t = q := by omega
        simpa [e] using hw

def physicalEdge {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ) (u : ℕ) : ℝˣ :=
  if h : u < m then Units.mk0 ((physicalSite ℓ θ u).weight) (by
    simp [physicalSite,PathSite.weight,h,(hp (fwd ⟨u,h⟩)).ne',(hp (back ⟨u,h⟩)).ne']) else 1

theorem edge_value {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ) (u : ℕ)
    (hu : u < m) : (physicalEdge ℓ θ hp u : ℝ) = (physicalSite ℓ θ u).weight := by
  simp [physicalEdge, hu]

/-- The central Jacobi representation of the physical chain, when the center is
at `l+1`. The size identity `l+r+2=m` says that the two arms exhaust the chain. -/
def physicalJoined {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ) (l r : ℕ) :
    Joined ℝ l r :=
  let d := fun t => (physicalSite ℓ θ t).diag
  let w := physicalEdge ℓ θ hp
  ⟨leftCode d w 0 l, rightCode d w (l+2) r, d (l+1), w l, w (l+1)⟩

theorem physicalJoined_branches {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ)
    (l r : ℕ) (hn : l+r+2=m) :
    let x := physicalJoined ℓ θ hp l r
    let f := physicalSite ℓ θ
    x.left.boundaryPair =
        (intervalCharpoly (sitesFrom f 0 (l+1)), intervalCharpoly (sitesFrom f 0 l)) ∧
    x.right.boundaryPair =
        (intervalCharpoly (sitesFrom f (l+2) (r+1)), intervalCharpoly (sitesFrom f (l+3) r)) := by
  constructor
  · exact left_pair _ _ _ _ (fun t _ h => edge_value ℓ θ hp t (by omega))
  · exact right_pair _ _ _ _ (fun t _ h => edge_value ℓ θ hp t (by omega))

theorem physicalJoined_determinant {m} (ℓ : Chamber m) (θ : Params m) (hp : Positive θ)
    (l r : ℕ) (hn : l+r+2=m) :
    (physicalJoined ℓ θ hp l r).determinant = intervalCharpoly (physicalSites ℓ θ) := by
  let f := physicalSite ℓ θ
  obtain ⟨hL,hR⟩ := physicalJoined_branches ℓ θ hp l r hn
  unfold Joined.determinant
  rw [hL,hR]
  dsimp only [physicalJoined, Prod.fst, Prod.snd]
  rw [edge_value ℓ θ hp l (by omega), edge_value ℓ θ hp (l+1) (by omega)]
  have hfull : physicalSites ℓ θ = sitesFrom f 0 l ++ f l :: f (l+1) :: f (l+2) ::
      sitesFrom f (l+3) r := by
    unfold physicalSites
    rw [show m+1=l+(r+3) by omega, from_append]
    simp only [Nat.zero_add,sitesFrom]
    rfl
  have hleft : sitesFrom f 0 (l+1) = sitesFrom f 0 l ++ [f l] := by
    rw [from_append]
    simp [sitesFrom]
  change _ = intervalCharpoly (physicalSites ℓ θ)
  rw [hfull,central_determinant]
  rw [← hleft]
  rfl

theorem rates_of_physicalJoined {m} (ℓ : Chamber m) (θ η : Params m)
    (hp : Positive θ) (hq : Positive η) (l r : ℕ) (hn : l+r+2=m)
    (he : physicalJoined ℓ θ hp l r = physicalJoined ℓ η hq l r) : θ = η := by
  let d := fun t => (physicalSite ℓ θ t).diag
  let e := fun t => (physicalSite ℓ η t).diag
  let v := physicalEdge ℓ θ hp
  let w := physicalEdge ℓ η hq
  obtain ⟨ld,lw⟩ := left_inj d e v w 0 l (congrArg Joined.left he)
  obtain ⟨rd,rw'⟩ := right_inj d e v w (l+2) r (congrArg Joined.right he)
  have cd : d (l+1) = e (l+1) := congrArg Joined.diagonal he
  have cl : v l = w l := congrArg Joined.leftEdge he
  have cr : v (l+1) = w (l+1) := congrArg Joined.rightEdge he
  simp only [Nat.zero_add] at ld lw
  apply PhysicalInverse.rates_of_diagonal_and_products ℓ θ η hp hq
  · intro c
    have dd : d c.val = e c.val := by
      by_cases h : c.val ≤ l
      · exact ld _ h
      by_cases h' : c.val = l+1
      · simpa only [h'] using cd
      have h₁ : c.val-(l+2) ≤ r := by have := c.isLt; omega
      simpa only [show l+2+(c.val-(l+2))=c.val by omega] using rd _ h₁
    simpa [d,e,physicalSite,c.isLt] using dd
  · intro k
    have de : v k.val = w k.val := by
      by_cases h : k.val < l
      · exact lw _ h
      by_cases h' : k.val = l
      · simpa only [h'] using cl
      by_cases h'' : k.val = l+1
      · simpa only [h''] using cr
      have h₁ : k.val-(l+2) < r := by have := k.isLt; omega
      simpa only [show l+2+(k.val-(l+2))=k.val by omega] using rw' _ h₁
    have z := congrArg (fun u : ℝˣ => (u : ℝ)) de
    simpa [v,w,edge_value,physicalSite,PathSite.weight,k.isLt,mul_comm] using z

end Catenary.Middle
