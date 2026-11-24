import Chain.EndpointExterior
import Chain.GlobalCounterexample

noncomputable section
namespace Catenary.GlobalMultiplicity
open Polynomial EndpointExterior Continuant
open scoped Polynomial

def third {m : ℕ} (hm : 3 ≤ m) : Chamber m := ⟨2, by omega⟩
def last (m : ℕ) : Chamber m := Fin.last m

theorem last_suffix {m} (ℓ : Chamber m) (x : Params m) :
    Middle.suffix ℓ x m = 1 := by
  unfold Middle.suffix
  rw [List.drop_eq_nil_of_le (by simp)]
  exact (charpoly_eq_cont ([] : List (PathSite ℝ))).trans Continuant.cont_nil

def F {m : ℕ} (hm : 3 ≤ m) (ℓ : Chamber m) (x : Params m) : Params m := fun r =>
  if r.val < m+1 then (Middle.full ℓ x).coeff r.val
  else if r.val < 2*m-1 then (Middle.suffix ℓ x 2).coeff (r.val-(m+1))
  else if r.val = 2*m-1 then gain ℓ (third hm) x else gain ℓ (last m) x

private theorem truncate_inj {a b : ℝ[X]} {d : ℕ} (ha : a.Monic) (hb : b.Monic)
    (da : a.natDegree = d) (db : b.natDegree = d) (hc : ∀ i < d, a.coeff i = b.coeff i) :
    a = b := by
  ext i
  rcases lt_trichotomy i d with hi | hi | hi
  · exact hc i hi
  · rw [hi, ← da, Polynomial.coeff_natDegree, ha, da, ← db, Polynomial.coeff_natDegree, hb]
  · rw [coeff_eq_zero_of_natDegree_lt (da ▸ hi), coeff_eq_zero_of_natDegree_lt (db ▸ hi)]

theorem data_iff_curves {m : ℕ} (hm : 3 ≤ m) (ℓ : Chamber m) (x y : Params m)
    (hx : Positive x) (hy : Positive y) :
    F hm ℓ x = F hm ℓ y ↔ SameCurves 0 (third hm) (last m) ℓ x y := by
  let j := third hm
  let k := last m
  have hD (z : Params m) : (Middle.full ℓ z).natDegree = m+1 := by
    simp [Middle.full, intervalCharpoly_natDegree]
  have hW (z : Params m) : (Middle.suffix ℓ z 2).natDegree = m-2 := by
    simp [Middle.suffix, intervalCharpoly_natDegree]
  have hs (z : Params m) : Middle.suffix ℓ z k.val = 1 := last_suffix ℓ z
  constructor
  · intro h
    have hd : Middle.full ℓ x = Middle.full ℓ y := by
      apply truncate_inj (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) (hD _) (hD _)
      intro i hi
      exact (by simpa [F,hi] using congrFun h (⟨i, by omega⟩ : Fin (2*m+1)))
    have hw : Middle.suffix ℓ x 2 = Middle.suffix ℓ y 2 := by
      apply truncate_inj (Matrix.charpoly_monic _) (Matrix.charpoly_monic _) (hW _) (hW _)
      intro i hi
      have ha : ¬ m+1+i < m+1 := by omega
      have hb : m+1+i < 2*m-1 := by omega
      simpa [F,ha,hb] using congrFun h (⟨m+1+i, by omega⟩ : Fin (2*m+1))
    have ha : ¬ 2*m-1 < m+1 := by omega
    have hb : ¬ 2*m < m+1 := by omega
    have hc : ¬ 2*m < 2*m-1 := by omega
    have he : 2*m ≠ 2*m-1 := by omega
    have hp : gain ℓ j x = gain ℓ j y := by
      simpa [F,ha,j] using congrFun h (⟨2*m-1, by omega⟩ : Fin (2*m+1))
    have hq : gain ℓ k x = gain ℓ k y := by
      simpa [F,hb,hc,he,k] using congrFun h (⟨2*m, by omega⟩ : Fin (2*m+1))
    apply (sameCurves_iff_common_regular 0 j k ℓ x y).mpr
    intro s u v
    constructor
    · rw [endpoint_transfer ℓ j x hx s u, endpoint_transfer ℓ j y hy s v, hd, hp]
      rw [show j.val = 2 from rfl, hw]
    · rw [endpoint_transfer ℓ k x hx s u, endpoint_transfer ℓ k y hy s v, hd, hq, hs, hs]
  · intro h
    have hr : SameCurves 0 k j ℓ x y := fun u hu t ht => (h u hu t ht).symm
    have cp : IsCoprime (Middle.full ℓ x) (Middle.suffix ℓ x k.val) := by rw [hs]; exact isCoprime_one_right
    obtain ⟨d,_,w,q,p⟩ := spectra_and_gains_of_curves ℓ k j x y hx hy cp hr
    have w' : Middle.suffix ℓ x 2 = Middle.suffix ℓ y 2 := w
    funext i
    simp only [F,d,w',show gain ℓ (third hm) x = _ from p,show gain ℓ (last m) x = _ from q]
    rfl

/-- An attainable fiber contains at least r distinct positive regular physical vectors. -/
def AtLeast {m : ℕ} (hm : 3 ≤ m) (ℓ : Chamber m) (r : ℕ) : Prop :=
  ∃ (y : Params m) (x : Fin r → Params m), Function.Injective x ∧
    ∀ t, Positive (x t) ∧ F hm ℓ (x t) = y ∧ (fderiv ℝ (F hm ℓ) (x t)).det ≠ 0

/-- Statement to be audited. A definition alone supplies no proof. -/
def SharpCount : Prop := ∀ (m : ℕ) (hm : 3 ≤ m) (ℓ : Chamber m),
  let r := if ℓ.val = 2 ∨ ℓ.val = m then 1 else 2
  AtLeast hm ℓ r ∧ ¬ AtLeast hm ℓ (r+1)

#print axioms data_iff_curves
end Catenary.GlobalMultiplicity
