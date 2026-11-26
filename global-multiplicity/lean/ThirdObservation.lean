import GlobalPhysical
import ThirdAdjacent
import ThirdSevenRegular
import Chain.EndpointExterior
import ThirdTerminal

/-! One-based indices in the note correspond to zero-based Fin indices here.
The full conjecture-to-kernel target is recorded separately from its proved
components, so an audit can test the exact statement rather than a name. -/
noncomputable section
namespace Catenary.ThirdObservation
open GlobalMultiplicity

def available {m : ℕ} (r : Chamber m) : Prop := r.val ≠ 2 ∧ r.val ≠ m

def guaranteed {m : ℕ} (r : Chamber m) : Prop :=
  m ≤ 5 ∨ r.val = 0 ∨ r.val = 1 ∨ r.val = 3

def EqualOutputs {m : ℕ} (hm : 3 ≤ m) (r ℓ : Chamber m) (x y : Params m) : Prop :=
  SameCurves 0 (Fin.last m) (third hm) ℓ x y ∧ SameCurves 0 (Fin.last m) r ℓ x y

def Uniqueness {m : ℕ} (hm : 3 ≤ m) (r ℓ : Chamber m) : Prop :=
  ∀ x y : Params m, Positive x → Positive y → EqualOutputs hm r ℓ x y → x = y

def Generic {m : ℕ} (hm : 3 ≤ m) (r ℓ : Chamber m) : Prop :=
  ∃ P : MvPolynomial (Fin (2*m+1)) ℝ,
    (∃ x : Params m, Positive x ∧ MvPolynomial.eval x P ≠ 0) ∧
    ∀ x y : Params m, Positive x → MvPolynomial.eval x P ≠ 0 →
      Positive y → EqualOutputs hm r ℓ x y → x = y

def RegularPair {m : ℕ} (hm : 3 ≤ m) (r ℓ : Chamber m) : Prop :=
  ∃ x y : Params m, Positive x ∧ Positive y ∧ x ≠ y ∧ EqualOutputs hm r ℓ x y ∧
    (fderiv ℝ (F hm ℓ) x).det ≠ 0 ∧ (fderiv ℝ (F hm ℓ) y).det ≠ 0

/-- The three conclusions of Theorem 1. A proposition definition alone does
not prove the general generic conclusion or the regular collision family. -/
def FullClassification : Prop :=
  ∀ (m : ℕ) (hm : 3 ≤ m) (r : Chamber m), available r →
    (∀ ℓ, Generic hm r ℓ) ∧
    ((∀ ℓ, Uniqueness hm r ℓ) ↔ guaranteed r) ∧
    (6 ≤ m → 4 ≤ r.val → RegularPair hm r 0)

theorem uniform_sufficiency {m : ℕ} (hm : 3 ≤ m) (r : Chamber m)
    (hr : available r) (h : guaranteed r) (ℓ : Chamber m) : Uniqueness hm r ℓ := by
  intro x y hx hy hc
  obtain ⟨h3, hR⟩ := hc
  have thirdVal : (third hm).val = 2 := rfl
  rcases hr with ⟨hr3,hrLast⟩
  have hlt := r.isLt
  by_cases h0 : r.val = 0
  · have eq : r = 0 := Fin.ext (by change r.val = 0; exact h0)
    rw [eq] at hR
    exact ThirdAdjacent.inlet_physical_unique ℓ x y hx hy hR
  by_cases h1 : r.val = 1
  · exact ThirdAdjacent.adjacent_physical_unique ℓ r (third hm) x y hx hy
      (by omega) (by omega) hR h3
  by_cases h4 : r.val = 3
  · by_cases hm5 : m = 4
    · subst m
      have heq : r = 3 := Fin.ext (by simpa using h4)
      subst r
      exact ThirdAdjacent.five_physical_unique ℓ x y hx hy h3 hR
    · exact ThirdAdjacent.adjacent_physical_unique ℓ (third hm) r x y hx hy
        (by omega) (by omega) h3 hR
  have small : m ≤ 5 := by rcases h with h | h | h | h <;> omega
  have hm6 : m = 5 := by omega
  subst m
  have heq : r = 4 := Fin.ext (by change r.val = 4; omega)
  subst r
  exact ThirdAdjacent.six_preterminal_physical_unique ℓ x y hx hy h3 hR

theorem generic_of_guaranteed {m : ℕ} (hm : 3 ≤ m) (r : Chamber m)
    (hr : available r) (h : guaranteed r) (ℓ : Chamber m) : Generic hm r ℓ := by
  refine ⟨1, ⟨fun _ => 1, fun _ => zero_lt_one, by simp⟩, ?_⟩
  intro x y hx _ hy he
  exact uniform_sufficiency hm r hr h ℓ x y hx hy he

/-- The middle range already follows from the earlier result for two outputs:
only observations at the third and the new site are needed. -/
theorem generic_middle {m : ℕ} (hm : 3 ≤ m) (r ℓ : Chamber m)
    (hl : 3 ≤ r.val) (hu : r.val + 2 ≤ m) : Generic hm r ℓ := by
  have ht : (third hm).val = 2 := rfl
  obtain ⟨P,hP,h⟩ := EndpointExterior.generic_global_small ℓ (third hm) r
    (by omega) (by change (third hm).val < r.val; omega) (by omega)
  refine ⟨P, ⟨_, SpectralPhysical.positive ℓ, by rw [hP]; norm_num⟩, ?_⟩
  intro x y hx he hy hc
  exact h x y hx hy he (fun u hu t ht => ⟨(hc.1 u hu t ht).2, (hc.2 u hu t ht).2⟩)

/-- The first assertion of Theorem 1 in physical rate coordinates. -/
theorem generic_all_sites {m : ℕ} (hm : 3 ≤ m) (r ℓ : Chamber m)
    (hr : available r) : Generic hm r ℓ := by
  by_cases h : guaranteed r
  · exact generic_of_guaranteed hm r hr h ℓ
  unfold guaranteed at h
  obtain ⟨h3,hn⟩ := hr
  have hrlt := r.isLt
  by_cases hpen : r.val+1 = m
  · obtain ⟨z,hz,hp⟩ := ThirdTerminal.positive_witness ℓ (by omega)
    refine ⟨ThirdTerminal.certificate ℓ, ⟨z,hz,hp⟩, ?_⟩
    intro x y hx hc hy he
    exact ThirdTerminal.physical_unique ℓ (third hm) r x y hx hy hm
      rfl hpen hc he.1 he.2
  · exact generic_middle hm r ℓ (by omega) (by omega)

theorem seven_not_uniform : ¬ Uniqueness (m:=6) (by decide) 5 4 := by
  rintro H
  obtain ⟨x,y,hx,hy,hd,ha,hb⟩ := ThirdSeven.physical_collision
  have swap {j k : Chamber 6} (h : SameCurves 0 j k 4 x y) : SameCurves 0 k j 4 x y :=
    fun u hu t ht => (h u hu t ht).symm
  exact hd (congrFun (H x y hx hy ⟨swap ha,swap hb⟩) (loss 6))

/-- The seven-site rational example is regular for the original two-output
physical map at both explicitly named rates. The leak is at site 5. -/
theorem seven_regular_pair : RegularPair (m:=6) (by decide) 5 4 := by
  let a := ThirdSevenRegular.overReal ThirdSeven.first
  let b := ThirdSevenRegular.overReal ThirdSeven.second
  obtain ⟨ha,hb,hneq,hcurves,hpen⟩ := ThirdSeven.named_collision
  have swap {j k : Chamber 6} (h : SameCurves 0 j k 4 a b) : SameCurves 0 k j 4 a b :=
    fun u hu t ht => (h u hu t ht).symm
  exact ⟨a,b,ha,hb,fun eq => hneq (congrFun eq (loss 6)), ⟨swap hcurves,swap hpen⟩,
    ThirdSevenRegular.physical_regular.1.ne,ThirdSevenRegular.physical_regular.2.ne'⟩

/-- The outstanding all-length physical statement, with an inlet leak. -/
def InletLeakCollisionFamily : Prop :=
  ∀ (m : ℕ) (hm : 3 ≤ m) (r : Chamber m), available r →
    6 ≤ m → 4 ≤ r.val → RegularPair hm r 0

/-- Once the inlet-leak collision family is supplied, all quantifiers in the
published classification follow. Conversely it is a clause of that theorem. -/
theorem full_iff_collision_family : FullClassification ↔ InletLeakCollisionFamily := by
  constructor
  · intro h m hm r hr
    exact (h m hm r hr).2.2
  · intro families m hm r hr
    refine ⟨fun ℓ => generic_all_sites hm r ℓ hr, ⟨?_, ?_⟩, families m hm r hr⟩
    · intro hu
      by_contra h
      unfold guaranteed at h
      have hr3 := hr.1
      obtain ⟨x,y,hx,hy,hxy,he,_,_⟩ := families m hm r hr (by omega) (by omega)
      exact hxy (hu 0 x y hx hy he)
    · intro hg ℓ
      exact uniform_sufficiency hm r hr hg ℓ

#print axioms uniform_sufficiency
#print axioms generic_middle
#print axioms full_iff_collision_family
#print axioms generic_all_sites
#print axioms seven_regular_pair
#print axioms seven_not_uniform
end Catenary.ThirdObservation
