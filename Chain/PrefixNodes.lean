import Chain.Spectral
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open Polynomial Catenary.Continuant
open scoped Polynomial
namespace Catenary.PrefixNodes

/-- A concrete p-site unit-edge block. Its p simple roots can avoid the roots
of any given nonzero tail polynomial. Every leading determinant at zero is
strictly positive, including the determinant of the entire prefix. -/
theorem choose (p : ℕ) (R : ℝ[X]) (hR : R ≠ 0) :
    ∃ start : ℕ, 0 < start ∧ ∃ nodes : Fin p → ℝ, Function.Injective nodes ∧
      (∀ t, (Spectral.block (List.range' start p)).eval (nodes t) = 0) ∧
      (∀ t, R.eval (nodes t) ≠ 0) ∧
      (∀ q : ℕ, 0 < (Spectral.block (List.range' start q)).eval 0) := by
  classical
  obtain ⟨lo,hlo⟩ := R.exists_min_root hR
  obtain ⟨s,hs⟩ := exists_nat_gt (-lo+3)
  let start := s+1
  have startpos : 0 < start := by dsimp [start]; omega
  let xs := List.range' start p
  have hdist := List.nodup_range' (s:=start) (n:=p)
  have hsimp := Spectral.simple_real_spectrum xs hdist
  let roots := (Spectral.block xs).roots.toFinset
  have hc : roots.card = p := by
    rw [show roots.card = (Spectral.block xs).roots.card from Multiset.toFinset_card_of_nodup hsimp.2,hsimp.1]
    simp [xs]
  let e : Fin p ≃ roots := (Finset.equivFinOfCardEq hc).symm
  let nodes (t : Fin p) : ℝ := (e t).val
  have root (t : Fin p) : (Spectral.block xs).eval (nodes t)=0 :=
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp (e t).property)
  refine ⟨start,startpos,nodes,Subtype.val_injective.comp e.injective,root,?_,?_⟩
  · intro t bad
    obtain ⟨u,hu,hnear⟩ := Spectral.real_root_near_label (root t)
    have hr := List.left_le_of_mem_range' (show u ∈ List.range' start p from hu)
    have hu' : (s:ℝ)+1≤u := by exact_mod_cast hr
    have h0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
    have hlt := (abs_lt.mp hnear).2
    have hbad := hlo (nodes t) bad
    linarith
  · intro q
    apply Spectral.positive_on_ray _ le_rfl
    intro u hu
    exact startpos.trans_le (List.left_le_of_mem_range' hu)

end Catenary.PrefixNodes
