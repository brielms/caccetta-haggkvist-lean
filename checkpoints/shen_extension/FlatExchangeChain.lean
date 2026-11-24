import checkpoints.shen_extension.FlatExchangeIntervals
import LeanCH.BR.BRWeightedPathExposure

namespace LeanCH.BR.Closure.FlatExchangeChain
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor FlatExchangeIntervals

/-- The labels are the vertices of the entire block in directed path order. -/
structure Chain (E : CH.Digraph) (L : Finset ℕ) (f : ℕ → ℕ) : Prop where
  span : (range L.card).image f=L
  injective : Set.InjOn f (range L.card)
  edge : ∀i<L.card,∀j<L.card,E (f i) (f j)=true ↔ j=i+1

theorem chain_of_connected {q E V B L} (free : QFree E V q) (cy : Cycle E V q B)
    (sub : L⊆B) (cap : L.card≤q) (live : L.Nonempty) (conn : Connected E L) :
    ∃f,Chain E L f := by
  classical
  have lf := free.mono_set (sub.trans cy.sub)
  obtain ⟨a,ha,start⟩ := exists_sink lf.reverse live cap
  obtain ⟨b,hb,finish,k,hk,w⟩ := reach_sink_of_card lf cap ha
  obtain ⟨f,f0,fk,edges⟩ := w.toFun
  let trace := (range (k+1)).image f
  have mem (i) (le : i≤k) : f i∈L := by
    cases i with
    | zero => rwa [f0]
    | succ i => exact (edges i (by omega)).1
  have key (i) (le : i≤k) : f i∈trace := mem_image.mpr ⟨i,mem_range.mpr (by omega),rfl⟩
  have trSub : trace⊆L := fun t ht => by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
    exact mem i (by have := mem_range.mp hi; omega)
  have succEq {u v v'} (hu : u∈L) (hv : v∈L) (hv' : v'∈L) (e : E u v=true) (e' : E u v'=true) : v=v' :=
    card_le_one.mp (cy.heads u (sub hu)).le _ (mem_outN.mpr ⟨sub hv,e⟩) _ (mem_outN.mpr ⟨sub hv',e'⟩)
  have predEq {v u u'} (hv : v∈L) (hu : u∈L) (hu' : u'∈L) (e : E u v=true) (e' : E u' v=true) : u=u' :=
    card_le_one.mp (cy.incoming v (sub hv)).le _ (mem_inN.mpr ⟨sub hu,e⟩) _ (mem_inN.mpr ⟨sub hu',e'⟩)
  have stays (u) (hu : u∈L) (v) (hv : v∈L) (arc : E u v=true) : u∈trace ↔ v∈trace := by
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      have hip := mem_range.mp hi
      by_cases eq : i=k
      · subst i; rw [fk] at arc; exact (finish _ hv arc).elim
      · have ne := edges i (by omega)
        exact (succEq hu hv ne.1 arc ne.2) ▸ key (i+1) (by omega)
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      have hip := mem_range.mp hi
      cases i with
      | zero => rw [f0] at arc; exact (start _ hu arc).elim
      | succ i =>
        have ne := edges i (by omega)
        exact (predEq hv hu (mem i (by omega)) arc ne.2) ▸ key i (by omega)
  have same : ConstantOnArcs E L (fun u => decide (u∈trace)) := by
    intro u hu v hv arc
    by_cases h : u∈trace
    · simp [h,(stays u hu v hv arc).mp h]
    · simp [h,mt (stays u hu v hv arc).mpr h]
  have span : trace=L := by
    apply Subset.antisymm trSub
    intro v hv
    have all := conn _ same (f 0) (mem 0 (by omega)) v hv
    simpa [key 0 (by omega)] using all.symm
  have inj := short_walk_index_injective lf (by omega : k≤q) f edges
  have count : k+1=L.card := by
    have eq := congrArg card span
    rw [show trace=(range (k+1)).image f from rfl,card_image_of_injOn inj,card_range] at eq
    exact eq
  refine ⟨f,⟨count ▸ span,count ▸ inj,?_⟩⟩
  intro i hi j hj
  constructor
  · intro arc
    by_cases ik : i=k
    · subst i; rw [fk] at arc; exact (finish _ (mem j (by omega)) arc).elim
    · have ne := edges i (by omega)
      have eq := succEq (mem i (by omega)) (mem j (by omega)) ne.1 arc ne.2
      exact inj (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) eq
  · rintro rfl
    exact (edges i (by omega)).2

#print axioms chain_of_connected

theorem Chain.mem {E L f} (P : Chain E L f) {i} (hi : i<L.card) : f i∈L := by
  rw [←P.span]
  exact mem_image.mpr ⟨i,mem_range.mpr hi,rfl⟩

theorem Chain.index {E L f} (P : Chain E L f) {a} (ha : a∈L) : ∃i<L.card,f i=a := by
  rw [←P.span] at ha
  obtain ⟨i,hi,eq⟩ := mem_image.mp ha
  exact ⟨i,mem_range.mp hi,eq⟩

private theorem Chain.walk_index {E L f} (P : Chain E L f) {a b k} (w : Walk E L a b k) :
    ∀ i<L.card,∀j<L.card,f i=a → f j=b → j=i+k := by
  induction w with
  | refl =>
    intro i hi j hj ea eb
    exact (P.injective (mem_range.mpr hj) (mem_range.mpr hi) (eb.trans ea.symm))
  | @step a t b k ht at' rest ih =>
    intro i hi j hj ea eb
    obtain ⟨s,hs,es⟩ := P.index ht
    have step := (P.edge i hi s hs).mp (by simpa [ea,es] using at')
    have bound := ih s hs j hj es eb
    omega

private theorem Chain.forward {E L f} (P : Chain E L f) {i j} (ij : i≤j) (hj : j<L.card) :
    Walk E L (f i) (f j) (j-i) := by
  apply walk_between (m:=j) _ ij le_rfl
  intro k hk
  exact ⟨P.mem (by omega), (P.edge k (by omega) (k+1) (by omega)).mpr rfl⟩

private theorem dest {S T : Finset ℕ} (e : ↥S ≃ ↥T)
    (fix : ∀a : ↥S,(a:ℕ)∈T → (e a:ℕ)=a) (a : ↥S) (na : (a:ℕ)∉T) : (e a:ℕ)∈T\S := by
  refine mem_sdiff.mpr ⟨(e a).property,fun h => ?_⟩
  have same : e ⟨e a,h⟩=e a := Subtype.ext (fix ⟨e a,h⟩ (e a).property)
  have eq : (e a:ℕ)=(a:ℕ) := congrArg Subtype.val (e.injective same)
  exact na (eq ▸ (e a).property)

private theorem aligned_chain {E S T f} (P : Chain E (S\T) f)
    (e : ↥S ≃ ↥T) (fix : ∀a : ↥S,(a:ℕ)∈T → (e a:ℕ)=a) (iso : ∀i j : ↥S,E i j=E (e i) (e j)) :
    ∃g,(T\S).card=(S\T).card ∧ Chain E (T\S) g ∧
      ∀ i (hi : i<(S\T).card),g i=(e ⟨f i,(mem_sdiff.mp (P.mem hi)).1⟩:ℕ) := by
  classical
  let m := (S\T).card
  let g (i : ℕ) := if h : i<m then (e ⟨f i,(mem_sdiff.mp (P.mem h)).1⟩ : ℕ) else 0
  have gi (i) (hi : i<m) : g i=(e ⟨f i,(mem_sdiff.mp (P.mem hi)).1⟩ : ℕ) := by simp [g,hi]
  have inj : Set.InjOn g (range m) := by
    intro i hi j hj eq
    rw [gi i (mem_range.mp hi),gi j (mem_range.mp hj)] at eq
    exact P.injective hi hj (congrArg Subtype.val (e.injective (Subtype.ext eq)))
  have span : (range m).image g=T\S := by
    ext y
    constructor
    · intro hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      rw [gi i (mem_range.mp hi)]
      exact dest e fix _ (mem_sdiff.mp (P.mem (mem_range.mp hi))).2
    · intro hy
      let y' : ↥T := ⟨y,(mem_sdiff.mp hy).1⟩
      have inv : (e.symm y' : ℕ)∈S\T := by
        refine mem_sdiff.mpr ⟨(e.symm y').property,fun overlap => ?_⟩
        have eq := fix (e.symm y') overlap
        rw [e.apply_symm_apply] at eq
        apply (mem_sdiff.mp hy).2
        change (y':ℕ)∈S
        rw [eq]
        exact (e.symm y').property
      obtain ⟨i,hi,eq⟩ := P.index inv
      have mapped : (⟨f i,(mem_sdiff.mp (P.mem hi)).1⟩:↥S)=e.symm y' := Subtype.ext eq
      exact mem_image.mpr ⟨i,mem_range.mpr hi,by rw [gi i hi,mapped,e.apply_symm_apply]⟩
  have eqm : (T\S).card=m := by rw [←span,card_image_of_injOn inj,card_range]
  refine ⟨g,eqm,⟨by rw [eqm]; exact span,by rw [eqm]; exact inj,?_⟩,gi⟩
  rw [eqm]
  intro i hi j hj
  rw [gi i hi,gi j hj,←iso]
  exact P.edge i hi j hj

/-- The indices of an actual cross arc can advance by at most one. -/
private theorem cross_index {q E V S T} {f g : ℕ→ℕ} (hq : 2≤q) (free : QFree E V q)
    (sat : BRsub.Sat q E S) (sv : S⊆V) (tv : T⊆V) (e : ↥S ≃ ↥T)
    (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) (iso : ∀i j : ↥S,E i j=E (e i) (e j))
    (P : Chain E (S\T) f) (map : ∀i (hi : i<(S\T).card),g i=(e ⟨f i,(mem_sdiff.mp (P.mem hi)).1⟩:ℕ))
    {i j} (hi : i<(S\T).card) (hj : j<(S\T).card) (cross : E (f i) (g j)=true) : j≤ i+1 := by
  cases arc : E (f i) (f j)
  · let u : ↥S := ⟨f i,(mem_sdiff.mp (P.mem hi)).1⟩
    let v : ↥S := ⟨f j,(mem_sdiff.mp (P.mem hj)).1⟩
    obtain ⟨k,_,w⟩ := FlatExchangeCycle.confined hq free sat sv tv e fix iso u v
      (by simpa only [map j hj] using cross) arc
    have bound := P.walk_index w j hj i hi rfl rfl
    omega
  · exact ((P.edge i hi j hj).mp arc).le

structure CrossOrder (q : ℕ) (E : CH.Digraph) (S T : Finset ℕ) (f g : ℕ→ℕ) : Prop where
  leftPath : Chain E (S\T) f
  rightPath : Chain E (T\S) g
  equalSize : (T\S).card=(S\T).card
  nextBound : ∀ i<(S\T).card,∀ j<(S\T).card,
    E (f i) (g j)=true ∨ E (g i) (f j)=true → j≤ i+1
  roundTrip : ∀i<(S\T).card,∀j<(S\T).card,∀k<(S\T).card,∀l<(S\T).card,
    E (f i) (g j)=true → E (g k) (f l)=true → j≤k → l≤ i → q<(k-j)+(i-l)+2

theorem cross_order {q E V S T f} (hq : 2≤q) (free : QFree E V q)
    (sSat : BRsub.Sat q E S) (tSat : BRsub.Sat q E T) (sv : S⊆V) (tv : T⊆V)
    (e : ↥S ≃ ↥T) (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) (iso : ∀i j : ↥S,E i j=E (e i) (e j))
    (P : Chain E (S\T) f) : ∃g,CrossOrder q E S T f g ∧
      ∀i (hi : i<(S\T).card),g i=(e ⟨f i,(mem_sdiff.mp (P.mem hi)).1⟩:ℕ) := by
  obtain ⟨g,size,Q,map⟩ := aligned_chain P e fix iso
  have rf (a : ↥T) (hs : (a:ℕ)∈S) : (e.symm a:ℕ)=a := by
    have eq : e ⟨a,hs⟩=a := Subtype.ext (fix ⟨a,hs⟩ a.property)
    exact congrArg Subtype.val (e.symm_apply_eq.mpr eq.symm)
  have ri (a b : ↥T) : E a b=E (e.symm a) (e.symm b) := by simpa using (iso (e.symm a) (e.symm b)).symm
  have back (i) (h : i<(T\S).card) : f i=(e.symm ⟨g i,(mem_sdiff.mp (Q.mem h)).1⟩:ℕ) := by
    have hs := size ▸ h
    let a : ↥S := ⟨f i,(mem_sdiff.mp (P.mem hs)).1⟩
    let b : ↥T := ⟨g i,(mem_sdiff.mp (Q.mem h)).1⟩
    have eq : b=e a := Subtype.ext (map i hs)
    exact congrArg Subtype.val ((e.symm_apply_eq.mpr eq).symm)
  refine ⟨g,⟨P,Q,size,?_,?_⟩,map⟩
  · intro i hi j hj h
    rcases h with h | h
    · exact cross_index hq free sSat sv tv e fix iso P map hi hj h
    · exact cross_index hq free tSat tv sv e.symm rf ri Q back (size.symm ▸ hi) (size.symm ▸ hj) h
  · intro i hi j hj k hk l hl ij kl jk li
    have left := (P.forward li hi).mono (sdiff_subset.trans sv)
    have right := (Q.forward jk (size.symm ▸ hk)).mono (sdiff_subset.trans tv)
    have w := (Walk.step (tv (mem_sdiff.mp (Q.mem (size.symm ▸ hj))).1) ij right).append
      (Walk.step (sv (mem_sdiff.mp (P.mem hl)).1) kl left)
    exact lt_of_not_ge fun low => free _ _ (by omega) (by omega) w

#print axioms cross_order

/-- Apply the ordered restriction at the actual pair of consecutive
repairs A,B and B,C. The mark supplies a vertex of B intersect C. -/
theorem step {q E V A B C} (hq : 2≤q) (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x : ℕ→ℚ} (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    (av : A⊆V) (cy : Cycle E V q B) (marked : (B∩C).Nonempty)
    (eqSize : (A\B).card=(B\C).card) :
    let S := V\(A\B)
    let T := V\(B\C)
    BRsub.Sat q E S → BRsub.Sat q E T → ∀e : ↥S ≃ ↥T,
    (∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) → FlatChildExchange.ExchangePattern E e →
      ((∃i j : ↥S,E i j=true ∧ E (e i) (e j)=false) ∧
       (∃i j : ↥S,E i j=false ∧ E (e i) (e j)=true)) ∨
      ((∀i j : ↥S,E i j=E (e i) (e j)) ∧ q<2*(B\C).card ∧
        ∃f g,CrossOrder q E S T f g ∧
          ∀i (_hi : i<(S\T).card),∃hs : f i∈S,g i=(e ⟨f i,hs⟩:ℕ)) := by
  classical
  intro S T ss ts e fix rule
  have left : S\T=B\C := by
    ext i
    have bv := @cy.sub i
    simp only [S,T,mem_sdiff]
    tauto
  have right : T\S=A\B := by
    ext i
    have inside := @av i
    simp only [S,T,mem_sdiff]
    tauto
  have covers : V⊆S∪T := by intro i hi; simp only [S,T,mem_union,mem_sdiff]; tauto
  have mcap : (B\C).card≤q := by
    have count := card_sdiff_add_card_inter B C
    rw [cy.size] at count
    have := card_pos.mpr marked
    omega
  have cap : (FlatExchangeCycle.moved S T).card≤2*(B\C).card := by
    unfold FlatExchangeCycle.moved
    rw [left,right]
    have bound := card_union_le (B\C) (A\B)
    omega
  rcases FlatExchangeCycle.frontier free small xp strict sdiff_subset sdiff_subset covers e fix rule with trade | ⟨iso,v,k,long,le,_⟩
  · exact Or.inl trade
  · change k ≤ (FlatExchangeCycle.moved S T).card at le
    have large := long.trans_le (le.trans cap)
    have room : (FlatExchangeCycle.moved S T).card≤2*q := by omega
    have live : (S\T).Nonempty := card_pos.mp (by rw [left]; omega)
    have conn := connected hq free small xp strict sdiff_subset sdiff_subset covers ss ts e fix iso room
    obtain ⟨f,P⟩ := chain_of_connected free cy (show S\T⊆B by rw [left]; exact sdiff_subset)
      (by rwa [left]) live conn
    obtain ⟨g,order,map⟩ := cross_order hq free ss ts sdiff_subset sdiff_subset e fix iso P
    exact Or.inr ⟨iso,by omega,f,g,order,fun i hi => ⟨(mem_sdiff.mp (P.mem hi)).1,map i hi⟩⟩

#print axioms step

/-- The order bound uses the mark and the same two laws picked in the
flat alternative of the schedule. -/
theorem on_mark {F q E V} (hq : 2≤q) (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x : ℕ→ℚ} (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    {s t : PairedFamilyLoop.State F} (av : PairedFamilyLoop.previous s⊆V)
    (cy : Cycle E V q (PairedFamilyLoop.current s))
    {send : ↥(PairedFamilyLoop.previous s) ≃ ↥(PairedFamilyLoop.previous t)}
    (mark : PairedFamilyLoop.previous t=PairedFamilyLoop.current s ∧
      ∃ b, ∃ r : ↥(PairedFamilyLoop.previous s), E b r=false ∧ E b (send r)=true ∧
        FullFamilySchedule.Mark q E V x s t send b (send r) r)
    (sz : (RawRepairAlternative.gone s).card=(RawRepairAlternative.gone t).card) :
    let S := V\RawRepairAlternative.gone s
    let T := V\RawRepairAlternative.gone t
    BRsub.Sat q E S → BRsub.Sat q E T → ∀e : ↥S ≃ ↥T,
    (∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) → FlatChildExchange.ExchangePattern E e →
      ((∃i j : ↥S,E i j=true ∧ E (e i) (e j)=false) ∧
       (∃i j : ↥S,E i j=false ∧ E (e i) (e j)=true)) ∨
      ((∀i j : ↥S,E i j=E (e i) (e j)) ∧ q<2*(RawRepairAlternative.gone t).card ∧
        ∃f g,CrossOrder q E S T f g ∧ ∀i (_hi : i<(S\T).card),∃hs : f i∈S,g i=(e ⟨f i,hs⟩:ℕ)) := by
  obtain ⟨join,b,r,_,_,_,_,_,_,shared,_⟩ := mark
  have overlap : (PairedFamilyLoop.current s∩PairedFamilyLoop.current t).Nonempty :=
    ⟨_,mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp shared).2).1,(mem_inter.mp shared).1⟩⟩
  dsimp only [RawRepairAlternative.gone]
  rw [join]
  exact step hq free small xp strict av cy overlap
    (by simpa only [RawRepairAlternative.gone,join] using sz)

#print axioms on_mark

end LeanCH.BR.Closure.FlatExchangeChain
