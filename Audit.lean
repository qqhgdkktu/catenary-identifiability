import Chain
import Chain.AxiomAudit

#audit_catenary

#print axioms Catenary.sameCurves_iff_common_regular
#print axioms Catenary.Endpoint.observed_endpoint_global
#print axioms Catenary.Endpoint.observed_endpoint_generic
#print axioms Catenary.sameCurves_iff_finite
#print axioms Catenary.physical_necessity
#print axioms Catenary.seven_negative
#print axioms Catenary.Cancellation.both_cancel
#print axioms Catenary.GlobalCounterexample.positive_global_counterexample
#print axioms Catenary.GlobalCounterexample.regular_derivatives
#print axioms Catenary.GlobalCounterexample.open_positive_ambiguity
#print axioms Catenary.Reflection.generic_reflect
#print axioms Catenary.trajectory_unique
#print axioms Catenary.physical_transfer_formula
#print axioms Catenary.genericLocalID_of_witness
#print axioms Catenary.FourBridge.four_genericLocalID
#print Catenary.PhysicalClassification

#print axioms Catenary.sameCurves_iff_nonnegative_inputs
#print axioms Catenary.physical_between
#print axioms Catenary.EndpointThreshold.generic_endpoint_threshold
#print axioms Catenary.WitnessVariation.common_root_recovers_entries
#print axioms Catenary.PrefixInstantiation.instantiated_rank
#print axioms Catenary.PrefixGeometry.physical_chart
#print axioms Catenary.PrefixPhysical.generic_of_physical_splice
#print axioms Catenary.physical_left_interior
#print axioms Catenary.physicalClassificationVerified
#print axioms Catenary.physicalClassification_int

example : Catenary.PhysicalClassification := Catenary.physicalClassificationVerified

-- Seven chambers. Moving only the far sensor changes the physical verdict.
example (ℓ : Catenary.Chamber 6) : Catenary.GenericLocalID (m:=6) 0 3 5 ℓ :=
  (Catenary.physicalClassificationVerified 6 (by decide) 0 3 5 ℓ (by decide)).mpr
    (by unfold Catenary.placement; decide)

example (ℓ : Catenary.Chamber 6) : ¬Catenary.GenericLocalID (m:=6) 0 3 6 ℓ :=
  Catenary.seven_negative ℓ

-- Both bounds at a strictly interior inlet with two sensors on the same side.
example (ℓ : Catenary.Chamber 7) : Catenary.GenericLocalID (m:=7) 1 4 6 ℓ :=
  (Catenary.physicalClassificationVerified 7 (by decide) 1 4 6 ℓ (by decide)).mpr
    (by unfold Catenary.placement; decide)

example (ℓ : Catenary.Chamber 7) : ¬Catenary.GenericLocalID (m:=7) 1 4 7 ℓ := by
  intro h
  have step := (Catenary.physicalClassificationVerified 7 (by decide) 1 4 7 ℓ (by decide)).mp h
  exact (by unfold Catenary.placement; decide : ¬Catenary.placement 8 2 5 8) step
