import Chain.Dynamics

namespace Catenary

/-- Zero initial conditions make comparison of the two unit step responses
equivalent to comparison under every continuous (known) input. -/
theorem sameCurves_iff_unit_input {m} (i j k ℓ : Chamber m) (θ η : Params m) :
    SameCurves i j k ℓ θ η ↔ ∀ t : ℝ, 0 ≤ t →
      amount (generator ℓ θ) i j (fun _ => 1) t = amount (generator ℓ η) i j (fun _ => 1) t ∧
      amount (generator ℓ θ) i k (fun _ => 1) t = amount (generator ℓ η) i k (fun _ => 1) t := by
  constructor
  · intro h
    exact h (fun _ => 1) continuous_const
  · intro h
    exact (sameCurves_iff_markov i j k ℓ θ η).mpr
      ⟨markov_eq_of_step (fun t ht => (h t ht).1), markov_eq_of_step (fun t ht => (h t ht).2)⟩

/-- Restricting continuous doses to nonnegative functions leaves the
equivalence relation on rates unchanged. -/
theorem sameCurves_iff_nonnegative_inputs {m} (i j k ℓ : Chamber m) (θ η : Params m) :
    SameCurves i j k ℓ θ η ↔ ∀ u : ℝ → ℝ, Continuous u → (∀ t, 0 ≤ u t) →
      ∀ t : ℝ, 0 ≤ t →
        (amount (generator ℓ θ) i j u t = amount (generator ℓ η) i j u t ∧
         amount (generator ℓ θ) i k u t = amount (generator ℓ η) i k u t) := by
  constructor
  · intro h u hu _
    exact h u hu
  · intro h
    exact (sameCurves_iff_unit_input i j k ℓ θ η).mpr (h (fun _ => 1) continuous_const (fun _ => zero_le_one))

end Catenary
