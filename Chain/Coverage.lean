import Chain.Reflection
import Chain.Endpoint
import Chain.FourBridge
import Chain.PublishedRule
import Chain.Obstruction

namespace Catenary

/-- If the inlet and a measured chamber coincide at the right-hand endpoint,
all positive physical vectors are separated, with arbitrary position of the leak. -/
theorem observed_right_endpoint_global {m} (j ℓ : Chamber m) (θ η : Params m)
    (hθ : Positive θ) (hη : Positive η)
    (hc : SameCurves (m:=m) (Fin.last m) j (Fin.last m) ℓ θ η) : θ = η := by
  have e := (Reflection.curves_reflect (Fin.last m) j (Fin.last m) ℓ θ η).mpr hc
  have h : SameCurves (m:=m) 0 0 j.rev ℓ.rev (Reflection.rates θ) (Reflection.rates η) := by
    simpa using e
  have he := Endpoint.observed_endpoint_global j.rev ℓ.rev _ _
    (fun c => hθ (Reflection.param c)) (fun c => hη (Reflection.param c)) h
  change Reflection.rates θ = Reflection.rates η at he
  simpa only [Reflection.rates_twice] using congrArg Reflection.rates he

theorem observed_right_endpoint_generic {m} (j ℓ : Chamber m) :
    GenericLocalID (m:=m) (Fin.last m) j (Fin.last m) ℓ := by
  apply (Reflection.generic_reflect (Fin.last m) j (Fin.last m) ℓ).mp
  simpa using Endpoint.observed_endpoint_generic j.rev ℓ.rev

/-- Reflected version of the verified four-chamber experiment. -/
theorem four_reflected (ℓ : Chamber 3) : GenericLocalID (m:=3) 3 0 1 ℓ := by
  have h := (Reflection.generic_reflect (m:=3) 0 2 3 ℓ.rev).mpr (FourBridge.four_genericLocalID ℓ.rev)
  rw [Fin.rev_rev] at h
  exact h

private theorem reflected_label {m} (v : Chamber m) :
    v.rev.val+1 = (m+1)+1-(v.val+1) := by
  have h := v.isLt
  simp [Fin.rev]
  omega

/-- Necessity of the diagram condition for every length, every position of the
inlet and distinct outputs, every positive vector domain and every known leak. -/
theorem physical_necessity {m} (i j k ℓ : Chamber m) (hjk : j < k) :
    GenericLocalID i j k ℓ → placement (m+1) (i.val+1) (j.val+1) (k.val+1) := by
  intro id
  by_contra bad
  by_cases hij : i < j
  · exact (Obstruction.not_generic_of_left_failure ℓ i j k hij hjk bad) id
  by_cases hki : k < i
  · have rjk : k.rev < j.rev := Fin.rev_lt_rev.mpr hjk
    have rij : i.rev < k.rev := Fin.rev_lt_rev.mpr hki
    have rbad : ¬placement (m+1) (i.rev.val+1) (k.rev.val+1) (j.rev.val+1) := by
      rw [reflected_label,reflected_label,reflected_label,placement_reflect]
      · exact bad
      all_goals first | exact i.isLt | exact j.isLt | exact k.isLt
    exact (Obstruction.not_generic_of_left_failure ℓ.rev i.rev k.rev j.rev rij rjk rbad)
      ((Reflection.generic_reflect i j k ℓ).mpr id)
  apply bad
  exact placement_middle (by have h : j.val ≤ i.val := le_of_not_gt hij; omega)
    (by have h : i.val ≤ k.val := le_of_not_gt hki; omega) k.isLt

/-- Boundary example with 7 chambers: all 13 rates fail joint generic local
identifiability from chambers 4 and 7, for every position of the single leak. -/
theorem seven_negative (ℓ : Chamber 6) : ¬GenericLocalID (m:=6) 0 3 6 ℓ := by
  intro h
  have e := physical_necessity (m:=6) 0 3 6 ℓ (by decide) h
  exact (by unfold placement; decide : ¬placement 7 1 4 7) e

end Catenary
