import checkpoints.shen_extension.TripleBankCuts

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Requests sharing the first leg of a return. -/
def returnGroup (D : CH.Digraph) (S : Finset ℕ) (f : ℕ → ℕ) (z w : ℕ) :=
  S.filter (fun x => f x = z ∧ D z w = true ∧ D w x = true)

/-- Each used first leg needs a distinct payer. A repeated first leg must
be paid at its tail. This matching criterion allows any number of rows
and any number of return paths through one blocker. -/
theorem unit_bank_hall {D : CH.Digraph} {V B P S : Finset ℕ} {s : ℕ} {f : ℕ → ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (sub : B ⊆ V) (pv : P ⊆ V)
    (common : ∀ b ∈ B, P ⊆ outN D V b)
    (rows : ∀ c, c ∈ S ↔ c ∈ V \ B ∧ 2 ≤ (outN D B c).card)
    (unit : ∀ a ∈ V \ B, (outN D B a).card ≤ 2)
    (fresh : ∀ c ∈ S, f c ∈ P ∧ D c (f c) ≠ true) :
    let U := V \ B
    let G := returnGroup D S f
    let E := (P ×ˢ U).filter (fun e => (G e.1 e.2).Nonempty)
    let pay (e : ↥E) : Finset ℕ :=
      if (G e.val.1 e.val.2).card ≤ 1 then {e.val.1,e.val.2} else {e.val.1}
    (∃ C : ℕ → Finset ℕ, QFree (patch D (unitAdds S f) C) U 3 ∧
      ∀ a ∈ U, s-1 ≤ (outN (patch D (unitAdds S f) C) U a).card) ↔
    ∀ X : Finset (↥E), X.card ≤ (X.biUnion pay).card := by
  classical
  intro U G E pay
  have add {a z} (ed : z ∈ unitAdds S f a) : a ∈ S ∧ z = f a := by
    by_cases h : a ∈ S
    · simpa [unitAdds,h] using ed
    · simp [unitAdds,h] at ed
  have atRow {x} (xs : x∈S) : f x ∈ unitAdds S f x := by simp [unitAdds,xs]
  have rel := fixed_menus_iff (A := unitAdds S f) safe reg sub pv common
    (fun _ _ _ ed => by
      obtain ⟨xs,rfl⟩ := add ed
      exact ⟨(fresh _ xs).1,((rows _).mp xs).2,(fresh _ xs).2⟩)
    (fun a au => by
      by_cases h : a∈S
      · simpa [unitAdds,h] using unit a au
      · have lim : (outN D B a).card≤1 := by
          by_contra! lim
          exact h ((rows a).mpr ⟨au,lim⟩)
        simpa [unitAdds,h] using lim)
  dsimp only at rel
  rw [rel,all_card_le_biUnion_card_iff_existsInjective']
  have spec {z w x} (hx : x∈G z w) :
      x∈S ∧ f x=z ∧ D z w=true ∧ D w x=true := mem_filter.mp hx
  have typed (e : ↥E) : e.val.1∈P ∧ e.val.2∈U := mem_product.mp (mem_filter.mp e.property).1
  have active (e : ↥E) : (G e.val.1 e.val.2).Nonempty := (mem_filter.mp e.property).2
  have inside {p} (pm : p∈P) : p∈U := mem_sdiff.mpr ⟨pv pm,fun pb =>
    loopfree safe (by decide) (pv pm) (mem_outN.mp (common p pb pm)).2⟩
  have outside (e : ↥E) : e.val.2∉P := by
    intro wp
    obtain ⟨x,hx⟩ := active e
    obtain ⟨xs,_,_,wx⟩ := spec hx
    obtain ⟨xu,hits⟩ := (rows _).mp xs
    obtain ⟨b,be⟩ := card_pos.mp (by omega : 0<(outN D B x).card)
    obtain ⟨bb,xb⟩ := mem_outN.mp be
    exact safe x 3 (by decide) (by decide) (.step (sub bb) xb (.step (pv wp)
      (mem_outN.mp (common b bb wp)).2 (.step (mem_sdiff.mp xu).1 wx (.refl _))))
  constructor
  · rintro ⟨C,cap,cover⟩
    let g (e : ↥E) := if e.val.2∈C e.val.1 then e.val.1 else e.val.2
    have second (e : ↥E) (off : e.val.2∉C e.val.1) {x} (hx : x∈G e.val.1 e.val.2) :
        x∈outN D U e.val.2 ∩ C e.val.2 := by
      obtain ⟨xs,fx,zw,wx⟩ := spec hx
      have t := cover x ((rows _).mp xs).1 (f x) (atRow xs) e.val.2 (typed e).2 (fx ▸ zw) wx
      rw [fx] at t
      exact mem_inter.mpr ⟨mem_outN.mpr ⟨((rows _).mp xs).1,wx⟩,t.resolve_left off⟩
    have first (e : ↥E) (on : e.val.2∈C e.val.1) :
        e.val.2∈outN D U e.val.1 ∩ C e.val.1 := by
      obtain ⟨x,hx⟩ := active e
      exact mem_inter.mpr ⟨mem_outN.mpr ⟨(typed e).2,(spec hx).2.2.1⟩,on⟩
    refine ⟨g,?_,?_⟩
    · intro e v eq
      by_cases he : e.val.2∈C e.val.1 <;> by_cases hv : v.val.2∈C v.val.1
      · simp [g,he,hv] at eq
        have h := first v hv
        rw [← eq] at h
        exact Subtype.ext (Prod.ext eq (card_le_one.mp (cap _ (inside (typed e).1)) _ (first e he) _ h))
      · simp [g,he,hv] at eq
        exact False.elim (outside v (eq ▸ (typed e).1))
      · simp [g,he,hv] at eq
        exact False.elim (outside e (eq.symm ▸ (typed v).1))
      · simp [g,he,hv] at eq
        obtain ⟨x,hx⟩ := active e
        obtain ⟨y,hy⟩ := active v
        have h := second v hv hy
        rw [←eq] at h
        have xy := card_le_one.mp (cap _ (typed e).2) _ (second e he hx) _ h
        exact Subtype.ext (Prod.ext ((spec hx).2.1.symm.trans ((congrArg f xy).trans (spec hy).2.1)) eq)
    · intro e
      by_cases h : e.val.2∈C e.val.1
      · by_cases n : (G e.val.1 e.val.2).card≤1 <;> simp [pay,g,h,n]
      · have n := (card_le_card (fun x hx => second e h hx)).trans (cap _ (typed e).2)
        simp [pay,g,h,n]
  · rintro ⟨g,inj,choice⟩
    let cuts (e : ↥E) := if g e=e.val.1 then {e.val.2} else G e.val.1 e.val.2
    let C (a : ℕ) := Finset.univ.biUnion (fun e : ↥E => if g e=a then cuts e else ∅)
    have pick (e : ↥E) : g e=e.val.1 ∨ (g e=e.val.2 ∧ (G e.val.1 e.val.2).card≤1) := by
      have h := choice e
      by_cases n : (G e.val.1 e.val.2).card≤1
      · simpa [pay,n] using h
      · exact Or.inl (by simpa [pay,n] using h)
    have low (e : ↥E) : (cuts e).card≤1 := by
      by_cases h : g e=e.val.1
      · simp [cuts,h]
      · simpa [cuts,h] using ((pick e).resolve_left h).2
    have memC {a x} : x∈C a ↔ ∃ e : ↥E, g e=a ∧ x∈cuts e := by
      constructor
      · intro h
        obtain ⟨e,_,hx⟩ := mem_biUnion.mp h
        by_cases he : g e=a
        · exact ⟨e,he,by simpa [he] using hx⟩
        · simp [he] at hx
      · rintro ⟨e,he,hx⟩
        exact mem_biUnion.mpr ⟨e,mem_univ _,by simpa [he] using hx⟩
    refine ⟨C,?_,?_⟩
    · intro a _
      apply (card_le_card inter_subset_right).trans
      apply card_le_one.mpr
      intro x hx y hy
      obtain ⟨e,ep,ex⟩ := memC.mp hx
      obtain ⟨v,vp,vy⟩ := memC.mp hy
      have eq := inj (ep.trans vp.symm)
      subst v
      exact card_le_one.mp (low e) _ ex _ vy
    · intro x _ z za w wu zw wx
      obtain ⟨xs,rfl⟩ := add za
      have hx : x∈G (f x) w := mem_filter.mpr ⟨xs,rfl,zw,wx⟩
      let e : ↥E := ⟨(f x,w),mem_filter.mpr ⟨mem_product.mpr ⟨(fresh _ xs).1,wu⟩,⟨x,hx⟩⟩⟩
      by_cases eq : g e=e.val.1
      · exact Or.inl (memC.mpr ⟨e,eq,by simp [cuts,eq,e]⟩)
      · exact Or.inr (memC.mpr ⟨e,((pick e).resolve_left eq).1,by simpa [cuts,eq,e] using hx⟩)

/-- On the actual top-order bank every assignment has more return groups
in some family than there are allowed payers for that family. -/
theorem unit_bank_deficit {D : CH.Digraph} {V B P : Finset ℕ} {s : ℕ} {f : ℕ → ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (order : V.card=3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (sub : B ⊆ V) (three : B.card=3) (pv : P ⊆ V)
    (common : ∀ b∈B, P⊆outN D V b)
    (unit : ∀ x∈V\B, (outN D B x).card≤2)
    (fresh : ∀ x∈V\B, 2≤(outN D B x).card → f x∈P ∧ D x (f x)≠true) :
    let U := V\B
    let S := U.filter (fun x => 2≤(outN D B x).card)
    let G := returnGroup D S f
    let E := (P ×ˢ U).filter (fun e => (G e.1 e.2).Nonempty)
    let pay (e : ↥E) : Finset ℕ :=
      if (G e.val.1 e.val.2).card ≤ 1 then {e.val.1,e.val.2} else {e.val.1}
    ∃ X : Finset (↥E), (X.biUnion pay).card < X.card := by
  classical
  intro U S G E pay
  by_contra! allFit
  have criterion := unit_bank_hall (S:=S) (f:=f) safe reg sub pv common
    (fun _ => mem_filter) unit (fun x h => fresh x (mem_filter.mp h).1 (mem_filter.mp h).2)
  obtain ⟨C,ok,floor⟩ := criterion.mpr allFit
  have size : U.card=3*(s-1) := by
    change (V\B).card=_
    rw [card_sdiff_of_subset sub,three,order]
    omega
  exact no _ U (card_pos.mp (by omega)) size.le ok floor

#print axioms unit_bank_deficit

#print axioms unit_bank_hall
end LeanCH.BR.TripleBank
