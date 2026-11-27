import checkpoints.shen_extension.CommonHeadTwoLayerCut

namespace LeanCH.BR.CommonHeadLastCut
open Finset BRq2 BRq3 BR45 FundedCascade BypassRepair BypassBankReplay JointShortcut
open scoped Classical

def Clash (D : CH.Digraph) (U : Finset ℕ) (q u z v w : ℕ) : Prop :=
  ∃ y∈U, D y u=true ∧ D y v=true ∧ Walk D U z y (q-2) ∧ Walk D U w y (q-2)

theorem Clash.flip {D U q u z v w} (both : Clash D U q u z v w) : Clash D U q v w u z := by
  obtain ⟨y,ys,yu,yv,zu,wv⟩ := both
  exact ⟨y,ys,yv,yu,wv,zu⟩

def Fits (D : CH.Digraph) (U P T : Finset ℕ) (q : ℕ) (f : ℕ → ℕ) : Prop :=
  (∀ u∈T, f u∈P ∧ D u (f u)≠true) ∧
  ∀ u∈T,∀ v∈T,u≠v → ¬Clash D U q u (f u) v (f v)

private theorem add_offer {D U P T q f u z} (fit : Fits D U P (T.erase u) q f)
    (allowed : z∈P ∧ D u z≠true)
    (clear : ∀ v∈T.erase u, ¬Clash D U q u z v (f v)) :
    ∃ g, Fits D U P T q g := by
  let g := fun v => if v=u then z else f v
  refine ⟨g,?_,?_⟩
  · intro v vt
    by_cases eq : v=u
    · simpa [g,eq] using allowed
    · simpa [g,eq] using fit.1 v (mem_erase.mpr ⟨eq,vt⟩)
  · intro a at' b bt ne both
    by_cases au : a=u
    · subst a
      have bu := Ne.symm ne
      exact clear b (mem_erase.mpr ⟨bu,bt⟩) (by simpa [g,bu] using both)
    by_cases bu : b=u
    · subst b
      exact clear a (mem_erase.mpr ⟨au,at'⟩) (by simpa [g,au] using both.flip)
    exact fit.2 a (mem_erase.mpr ⟨au,at'⟩) b (mem_erase.mpr ⟨bu,bt⟩) ne (by simpa [g,au,bu] using both)

/-- On an inclusion-minimal unpayable set, every target of a removed row
collides with any fixed valid assignment on the rest, at a specific payer. -/
theorem minimal_clash {D U P S q} (impossible : ¬∃ f, Fits D U P S q f) :
    ∃ T⊆S, T.Nonempty ∧ (∀ u∈T, ∃ f, Fits D U P (T.erase u) q f) ∧
      ∀ u∈T,∀ f, Fits D U P (T.erase u) q f → ∀ z∈P, D u z≠true →
        ∃ v∈T.erase u, Clash D U q u z v (f v) := by
  classical
  let bad := S.powerset.filter (fun A => ¬∃ f, Fits D U P A q f)
  have sb : S∈bad := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl,impossible⟩
  obtain ⟨T,tm,least⟩ := bad.exists_min_image card ⟨S,sb⟩
  obtain ⟨power,no⟩ := mem_filter.mp tm
  have ts := mem_powerset.mp power
  have live : T.Nonempty := by
    by_contra! empty
    subst T
    exact no ⟨fun _ => 0,by simp [Fits]⟩
  refine ⟨T,ts,live,?_,?_⟩
  · intro u ut
    by_contra noSmaller
    have small : T.erase u∈bad := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset ..).trans ts),noSmaller⟩
    exact (Nat.not_le_of_lt (card_erase_lt_of_mem ut)) (least _ small)
  · intro u _ f fit z zp fresh
    by_contra! clear
    exact no (add_offer fit ⟨zp,fresh⟩ clear)

/-- A retained subset of short rows whose missing common targets each
have at least two misses on that subset. The payer sees both rows, and is
reachable from both actual targets. -/
theorem shared_core {q s} {X : ShenMinimumOrder.Source q s} {m : Cell}
    (cert : SelectedParentOrder X m) (shared : JointShortcutReplay.SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
    (reg : OutEq s X.D X.V) (hs : 2≤s) (hq : 3≤q) (none : NoHost q (s-1)) :
    ∃ p∈X.V,∃ h∈X.V,p≠h ∧
      let P := heads X.D X.V p h
      let S := jointParents X.D X.V p h
      let U := X.V \ {p,h}
      (∀ a∈X.V,∀ b∈X.V,a≠b → (heads X.D X.V a b).card≤P.card) ∧
      (∀ u∈S,∃ z∈P,X.D u z≠true) ∧
      ∃ T⊆S, T.Nonempty ∧ (∀ u∈T,∃ f,Fits X.D U P (T.erase u) q f) ∧
      ∀ u∈T,∀ f,Fits X.D U P (T.erase u) q f → ∀ z∈P,X.D u z≠true →
        ∃ v∈T.erase u, Clash X.D U q u z v (f v) ∧ X.D v z≠true ∧ X.D u (f v)≠true := by
  classical
  have order := cert.shared.mp shared
  have pos : 0<q*(s-1) := Nat.mul_pos (by omega) (by omega)
  obtain ⟨p,pv,h,hv,ph,best,miss⟩ := select_bank X.free (by omega) (show 2≤X.V.card by omega)
  let S := jointParents X.D X.V p h
  let P := heads X.D X.V p h
  let U := X.V \ {p,h}
  have bs : ({p,h} : Finset ℕ)⊆X.V := insert_subset pv (singleton_subset_iff.mpr hv)
  have two : ({p,h} : Finset ℕ).card=2 := card_pair ph
  have bank : Eligible X.V {p,h} q (s-1) := ⟨bs,by rw [two,order]; omega,
    card_pos.mp (by rw [card_sdiff_of_subset bs,two,order]; omega)⟩
  have no : ¬∃ f, Fits X.D U P S q f := by
    rintro ⟨f,fit⟩
    obtain ⟨y,ym,_,u,us,v,vs,ne,yu,yv,wu,wv,_⟩ :=
      collision X.free hq reg hs pv hv ph bank none f fit.1
    exact fit.2 u us v vs ne ⟨y,ym,yu,yv,wu,wv⟩
  obtain ⟨T,ts,live,rest,allhit⟩ := minimal_clash no
  refine ⟨p,pv,h,hv,ph,best,miss,T,ts,live,rest,?_⟩
  intro u ut f fit z zp fresh
  obtain ⟨v,vs,clash⟩ := allhit u ut f fit z zp fresh
  obtain ⟨y,ym,yu,yv,wu,wv⟩ := clash
  have um := ts ut
  have vm := ts (mem_of_mem_erase vs)
  have uv := (mem_inN.mp (mem_inN.mp um).1).1
  have vv := (mem_inN.mp (mem_inN.mp vm).1).1
  exact ⟨v,vs,⟨y,ym,yu,yv,wu,wv⟩,fun vz => no_back X.free (by omega) sdiff_subset vv
    (outN_subset (mem_inter.mp zp).1) wu vz yv,fun uz => no_back X.free (by omega) sdiff_subset uv
    (outN_subset (mem_inter.mp (fit.1 v vs).1).1) wv uz yu⟩

#print axioms minimal_clash
#print axioms shared_core
end LeanCH.BR.CommonHeadLastCut
