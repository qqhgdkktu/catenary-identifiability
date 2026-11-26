import Chain.PrefixTransfer

/-! A boundary point of physical parameter space used solely to show that
the determinant for a penultimate sensor is a nonzero polynomial. The last
three chambers have zero diagonal and no backwards link to the shortened
chain. Its terminal leak is redirected along the new one-way joining edge. -/
noncomputable section
namespace Catenary.ThirdTerminalWitness
open Polynomial Continuant PhysicalInverse Middle
open scoped Polynomial

private theorem phys_diag {m} (ℓ : Chamber m) (x : Params m) (i : ℕ) (hi : i ≤ m) :
    -(physicalSite ℓ x i).diag = a x i + prev x i + (if i=ℓ.val then x (loss m) else 0) := by
  simpa [physicalSite,show i<m+1 by omega] using diag_total ℓ (⟨i,by omega⟩ : Chamber m) x

private theorem add_inert (f : ℕ → PathSite ℝ) (u q : ℕ)
    (hd : (f (u+q+1)).diag = 0) (hb : (f (u+q)).weight = 0) :
    intervalCharpoly (sitesFrom f u (q+2)) = X * intervalCharpoly (sitesFrom f u (q+1)) := by
  have single (z : PathSite ℝ) : intervalCharpoly [z] = X-C z.diag :=
    (charpoly_eq_cont _).trans (cont_singleton _)
  have eq := charpoly_cut (sitesFrom f u q) [] (f (u+q)) (f (u+q+1))
  rw [Closed.sites_snoc f u (q+1),Closed.sites_snoc f u q]
  simpa [single, List.append_assoc, Nat.add_assoc, hd, hb, mul_comm,
    show (f (u+(q+1))).diag = 0 by simpa only [Nat.add_assoc] using hd] using eq

theorem three_inert_chambers {m} (ℓ : Chamber m) (hm : 6 ≤ m) :
    ∃ (x : Params m) (D₀ W₀ : ℝ[X]), full ℓ x = X^3*D₀ ∧ suffix ℓ x 2 = X^3*W₀ ∧
      D₀.Monic ∧ D₀.natDegree = m-2 ∧ IsCoprime D₀ W₀ := by
  obtain ⟨t,rfl⟩ : ∃ t, m=t+3 := ⟨m-3,by omega⟩
  let z := SpectralPhysical.rates (Fin.last t)
  let forward (i : Fin (t+3)) := a z i.val + if i.val=t then z (loss t) else 0
  let backwards (i : Fin (t+3)) := b z i.val
  let x := Gauge.pack forward backwards 0
  let f := physicalSite ℓ x
  let g := physicalSite (Fin.last t) z
  have ax (i : ℕ) : a x i = a z i + (if i=t then z (loss t) else 0) := by
    by_cases h : i<t+3
    · simp only [a,x,h,dif_pos,Gauge.pack_fwd,forward]
    · simp [a,x,h,show ¬i<t by omega,show i≠t by omega]
  have bx (i : ℕ) : b x i = b z i := by
    by_cases h : i<t+3
    · simp only [b,x,h,dif_pos,Gauge.pack_back,backwards]
    · simp [b,h,show ¬i<t by omega]
  have px (i : ℕ) : prev x i = prev z i := by cases i <;> simp [prev,bx]
  have dx (i : ℕ) (hi : i≤t) : (f i).diag = (g i).diag := by
    apply neg_injective
    rw [phys_diag ℓ x i (by omega),phys_diag (Fin.last t) z i hi,ax,px]
    simp [x,Fin.val_last]; ring
  have product {k} (v : Chamber k) (p : Params k) (i : ℕ) :
      (physicalSite v p i).weight = b p i * a p i := rfl
  have wx (i : ℕ) (hi : i<t) : (f i).weight = (g i).weight := by
    simp only [f,g,product,bx,ax,if_neg (Nat.ne_of_lt hi),add_zero]
  have dz (i : ℕ) (hi : t < i) (hi' : i≤t+3) : (f i).diag=0 := by
    have prevz : prev z i = 0 := by
      cases i with
      | zero => omega
      | succ i => simp [prev,b,show ¬i<t by omega]
    have h := phys_diag ℓ x i hi'
    rw [ax,px,prevz,show a z i=0 by simp [a,show ¬i<t by omega],
      show x (loss (t+3))=0 by simp [x]] at h
    simpa [f,show i≠t by omega] using h
  have wz (i : ℕ) (hi : t ≤ i) : (f i).weight=0 := by
    simp only [f,product,bx]
    rw [show b z i=0 by simp [b,show ¬i<t by omega],zero_mul]
  have extend (u q : ℕ) (hu : u+q=t) :
      intervalCharpoly (sitesFrom f u (q+4)) = X^3*intervalCharpoly (sitesFrom g u (q+1)) := by
    have base : intervalCharpoly (sitesFrom f u (q+1)) =
        intervalCharpoly (sitesFrom g u (q+1)) :=
      PrefixPhysical.interval_of_entries _ _ _ _ _ (fun i hi => dx _ (by omega))
        (fun i hi => wx _ (by omega))
    rw [add_inert f u (q+2) (dz _ (by omega) (by omega)) (wz _ (by omega)),
      add_inert f u (q+1) (dz _ (by omega) (by omega)) (wz _ (by omega)),
      add_inert f u q (dz _ (by omega) (by omega)) (wz _ (by omega)),base]
    ring
  let j : Chamber t := ⟨2,by omega⟩
  let D₀ := full (Fin.last t) z
  let W₀ := suffix (Fin.last t) z j.val
  refine ⟨x,D₀,W₀,extend 0 t (by omega),?_,Matrix.charpoly_monic _,?_,?_⟩
  · change intervalCharpoly ((sitesFrom f 0 (t+3+1)).drop (2+1)) =
      X^3*intervalCharpoly ((sitesFrom g 0 (t+1)).drop (2+1))
    rw [drop_from _ _ _ _ (by omega),drop_from _ _ _ _ (by omega)]
    rw [show t+3+1-(2+1)=(t-3)+4 by omega,show t+1-(2+1)=(t-3)+1 by omega]
    exact extend 3 (t-3) (by omega)
  · simp [D₀,full,intervalCharpoly_natDegree,physicalSites_length]
  · exact (SpectralPhysical.no_cancellation (Fin.last t) 0 j).of_mul_right_right

#print axioms three_inert_chambers
end Catenary.ThirdTerminalWitness
