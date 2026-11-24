import Chain.Between
import Chain.EndpointThreshold

/-! Reflection and endpoint cases of the diagram classification. Only the
strictly internal exterior inlet needs a splice. -/
namespace Catenary

def LeftInteriorSuffices : Prop :=
  ∀ {m : ℕ} (i j k ℓ : Chamber m), 0 < i.val → i < j → j < k →
    j.val-i.val ≤ m-k.val+2 → GenericLocalID i j k ℓ

private theorem left_sufficient (lift : LeftInteriorSuffices) {m} (i j k ℓ : Chamber m)
    (hij : i < j) (hjk : j < k) (pos : placement (m+1) (i.val+1) (j.val+1) (k.val+1)) :
    GenericLocalID i j k ℓ := by
  have ij : i.val < j.val := hij
  have kk := k.isLt
  have small : j.val-i.val ≤ m-k.val+2 := by unfold placement at pos; omega
  by_cases hi : i.val=0
  · have e : i=0 := Fin.ext hi
    subst i
    exact EndpointThreshold.generic_endpoint_threshold ℓ j k (by simpa using ij) hjk (by simpa using small)
  exact lift i j k ℓ (by omega) hij hjk small

theorem complete_from_left (lift : LeftInteriorSuffices) : PhysicalClassification := by
  intro m _ i j k ℓ hjk
  refine ⟨physical_necessity i j k ℓ hjk,?_⟩
  intro pos
  by_cases hij : i < j
  · exact left_sufficient lift i j k ℓ hij hjk pos
  by_cases hki : k < i
  · apply (Reflection.generic_reflect i j k ℓ).mp
    have ri : i.rev < k.rev := Fin.rev_lt_rev.mpr hki
    have rj : k.rev < j.rev := Fin.rev_lt_rev.mpr hjk
    apply left_sufficient lift i.rev k.rev j.rev ℓ.rev ri rj
    have lab (v : Chamber m) : v.rev.val+1 = (m+1)+1-(v.val+1) := by
      have h := v.isLt
      simp [Fin.rev]
      omega
    simpa only [lab,placement_reflect i.isLt j.isLt k.isLt] using pos
  exact physical_between i j k ℓ (le_of_not_gt hij) (le_of_not_gt hki)

end Catenary
