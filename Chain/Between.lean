import Chain.SeparatedWitness
import Chain.CoprimeWitness
import Chain.Coverage

namespace Catenary

/-- For every chain length and every leak, an inlet between the two sensors,
including either sensor, makes all original physical rates generically locally
identifiable. No unproved spectral or observability assumption remains. -/
theorem physical_between {m} (i j k ℓ : Chamber m) (hji : j ≤ i) (hik : i ≤ k) :
    GenericLocalID i j k ℓ := by
  by_cases left : i.val = 0
  · have ji : j = 0 := Fin.ext (by change j.val = 0; have h : j.val ≤ i.val := hji; omega)
    have ii : i = 0 := Fin.ext left
    subst i
    subst j
    exact Endpoint.observed_endpoint_generic k ℓ
  by_cases right : i.val = m
  · have kmax : k = Fin.last m := Fin.ext (by have h := k.isLt; have h' : i.val ≤ k.val := hik; simpa using (by omega : k.val=m))
    have imax : i = Fin.last m := Fin.ext right
    subst i
    subst k
    exact observed_right_endpoint_generic j ℓ
  have hi := i.isLt
  apply CoprimeWitness.generic_middle_of_witness i j k ℓ (by omega) (by omega) hji hik
    (SpectralPhysical.rates ℓ) (SpectralPhysical.positive ℓ)
  · exact SpectralPhysical.separated_branches ℓ i
  · exact SpectralPhysical.no_cancellation ℓ j i

end Catenary
