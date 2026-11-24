import Chain.Assembly
import Chain.PrefixGeometry
import Chain.PrefixTransfer

/-! The position-only classification for the original forced ODE, with one
known leak location and all directed rates and the leak rate unknown. -/
namespace Catenary

/-- Reattach the prefix strictly to the left of an interior inlet with two
sensors to its right. The auxiliary signed realization certifies a polynomial
minor and hence a generic local statement on strictly positive rates. -/
theorem physical_left_interior : LeftInteriorSuffices := by
  intro m i j k ℓ hi hij hjk small
  have ij : i.val < j.val := hij
  have jk : j.val < k.val := hjk
  have kk := k.isLt
  let p := i.val-1
  let n := m-i.val
  let a : Chamber n := ⟨j.val-i.val, by dsimp [n]; omega⟩
  let b : Chamber n := ⟨k.val-i.val, by dsimp [n]; omega⟩
  have hm : p+1+n=m := by dsimp [p,n]; omega
  have hip : i.val=p+1 := by dsimp [p]; omega
  have hja : j.val=p+1+a.val := by dsimp [p,a]; omega
  have hkb : k.val=p+1+b.val := by dsimp [p,b]; omega
  have ha : 0 < a.val := by dsimp [a]; omega
  have hb : 0 < b.val := by dsimp [b]; omega
  have ab : a < b := by change a.val < b.val; omega
  have cut : a.val ≤ n-b.val+2 := by dsimp [a,n,b]; omega
  obtain ⟨z,hz,start,hs,nodes,hn,roots,β,hβ,_,rank⟩ :=
    PrefixInstantiation.instantiated_rank p a b ha ab cut 1 zero_lt_one
  obtain ⟨x,hx,hedges,coords⟩ := PrefixGeometry.physical_chart ℓ p n hm start hs nodes z β hz hβ
  let S := PrefixInstantiation.leftPoly start (p+1)
  apply PrefixPhysical.generic_of_physical_splice ℓ i j k a b hm hip hja hkb ha hb nodes hn S
    (Spectral.block_monic _) (by simp [S,PrefixInstantiation.leftPoly,Spectral.block_natDegree]) roots x hx hedges
  change Function.Injective (fderiv ℝ (PrefixInstantiation.chart a b nodes S)
    (PrefixPhysical.coordinates ℓ p n nodes (PrefixGeometry.S start p) x))
  rw [coords]
  exact rank

/-- All 2n−1 rates are jointly generically locally identifiable exactly at
the stated placements, for every n≥3 and every known leak chamber. -/
theorem physicalClassificationVerified : PhysicalClassification :=
  complete_from_left physical_left_interior

/-- Ordinary integer subtraction gives the same statement with the two
inclusive inequalities printed in the manuscript, in one-based labels. -/
theorem physicalClassification_int {m : ℕ} (hm : 2 ≤ m) (i j k ℓ : Chamber m) (hjk : j < k) :
    GenericLocalID i j k ℓ ↔
      ((j.val+1 : ℤ)+(k.val+1 : ℤ)-(m+1 : ℤ)-2 ≤ (i.val+1 : ℤ) ∧
       (i.val+1 : ℤ) ≤ (j.val+1 : ℤ)+(k.val+1 : ℤ)+1) := by
  simpa only [Nat.cast_add,Nat.cast_one] using
    (physicalClassificationVerified m hm i j k ℓ hjk).trans
      (placement_int (m+1) (i.val+1) (j.val+1) (k.val+1))

end Catenary
