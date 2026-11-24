import checkpoints.shen_extension.MinimumRootColumn
import checkpoints.shen_extension.PuncturedSquareRoles

namespace LeanCH.BR.Closure.MinimumOrbitEscape
open Finset BRq2 BRq3 BR45 BRsub ShenCycleSuccessor ShortestCycleWeights PuncturedSquareRoles

/-- If the whole fixed path feeds the deleted root, at least one retained
square joins an exterior label to b or to a moving label. -/
theorem root_bridge {n} (X : Model 3 n) {h b P S} (hv : h∈X.V)
    (ps : P.card=3) (cs : Cycle X.D (X.V\{h}) 3 S)
    (fits : ∀x∈S,Cycle X.D (X.V\{h}) 3 (insert x P))
    (bp : b∈P) (sb : ∀x∈S,X.D x b=true) (allP : ∀p∈P,X.D p h=true)
    (large : 2≤((X.V\{h})\(P∪S)).card) :
    ∃r∈insert b S,∃t∈(X.V\{h})\(P∪S),∃N,Cycle X.D (X.V\{h}) 3 N ∧ r∈N ∧ t∈N := by
  classical
  let W := X.V\{h}
  let U := P∪S
  let T := W\U
  have sz := cs.size
  obtain ⟨s,ss⟩ := card_pos.mp (by omega : 0<S.card)
  have pw : P⊆W := fun _ zp => (fits s ss).sub (mem_insert_of_mem zp)
  have uw : U⊆W := union_subset pw cs.sub
  have tw : T⊆W := sdiff_subset
  have wv : W⊆X.V := sdiff_subset
  have window (z) (zv : z∈X.V) (zh : z≠h) : z∈W := mem_sdiff.mpr ⟨zv,by simpa using zh⟩
  have away (z) (zw : z∈W) : z≠h := by simpa using (mem_sdiff.mp zw).2
  have inside (z) (zw : z∈W) (zt : z∉T) : z∈U := by
    by_contra zu
    exact zt (mem_sdiff.mpr ⟨zw,zu⟩)
  have label : insert b S⊆U := insert_subset (mem_union_left _ bp) subset_union_right
  have forbids_module (A : Finset ℕ) (aw : A⊆W) (two : 2≤A.card) (out : OutUniform X.D X.V A) : False :=
    X.prime A (aw.trans wv) two (fun eq => away h (aw (eq.symm ▸ hv)) rfl)
      ⟨out,outUniform_inUniform X.free X.sat (aw.trans wv) out⟩
  have noBack (x) (xs : x∈S) : outN X.D (insert x P) h=∅ := by
    have sub : P⊆inN X.D (insert x P) h := fun p pp => mem_inN.mpr ⟨mem_insert_of_mem pp,allP p pp⟩
    exact cycle_three_feeds_no_return (by decide) X.free ((fits x xs).sub.trans wv) (fits x xs).size
      (fits x xs).heads hv (ps.ge.trans (card_le_card sub))
  have noHS (x) (xs : x∈S) : X.D h x=false := Bool.eq_false_iff.mpr fun hx =>
    (by have hit : x∈outN X.D (insert x P) h := mem_outN.mpr ⟨mem_insert_self _ _,hx⟩; rw [noBack x xs] at hit; exact notMem_empty x hit)
  have formP (p) (pp : p∈P) := parent_role X hv (wv (pw pp)) (allP p pp)
  by_contra miss
  have pair (r) (rr : r∈insert b S) (t) (tt : t∈T) := forced X (wv (uw (label rr))) (wv (tw tt))
    (away r (uw (label rr))) (away t (tw tt)) (fun e => (mem_sdiff.mp tt).2 (e ▸ label rr))
    (fun ex => miss ⟨r,rr,t,tt,ex⟩)
  have backpair (t) (tt : t∈T) (r) (rr : r∈insert b S) := forced X (wv (tw tt)) (wv (uw (label rr)))
    (away t (tw tt)) (away r (uw (label rr))) (fun e => (mem_sdiff.mp tt).2 (e.symm ▸ label rr))
    (fun ⟨N,c,tn,rn⟩ => miss ⟨r,rr,t,tt,N,c,rn,tn⟩)
  have noTP (t) (tt : t∈T) : role X.D h t≠.parent := fun eq =>
    (pair b (mem_insert_self _ _) t tt).1 ((formP b bp).trans eq.symm)
  have triangle {i j k} (iv : i∈X.V) (jv : j∈X.V) (kv : k∈X.V)
      (ij : X.D i j=true) (jk : X.D j k=true) : X.D k i=false :=
    Bool.eq_false_iff.mpr fun ki => X.free i 3 (by decide) le_rfl (.step jv ij (.step kv jk (.step iv ki (.refl _))))
  by_cases mixed : ∃x∈S, X.D x h=false
  · obtain ⟨x,xs,xh⟩ := mixed
    have opposite : role X.D h x=.opposite := by simp [role,noHS x xs,xh]
    have heads (t) (tt : t∈T) : role X.D h t=.head := by
      cases e : role X.D h t with
      | head => rfl
      | parent => exact False.elim (noTP t tt e)
      | opposite => exact False.elim ((pair x (mem_insert_of_mem xs) t tt).1 (opposite.trans e.symm))
    apply forbids_module T tw large
    intro i ii j jj z zv zt
    have ih := head_arc (heads i ii)
    have jh := head_arc (heads j jj)
    by_cases eq : z=h
    · subst z
      rw [Bool.eq_false_iff.mpr (digonfree X.free (by decide) hv (wv (tw ii)) ih),
        Bool.eq_false_iff.mpr (digonfree X.free (by decide) hv (wv (tw jj)) jh)]
    have zu := inside z (window z zv eq) zt
    by_cases zh : X.D z h=true
    · rw [triangle zv hv (wv (tw ii)) zh ih,triangle zv hv (wv (tw jj)) zh jh]
    have zs : z∈S := (mem_union.mp zu).resolve_left (fun zp => zh (allP z zp))
    have zr : role X.D h z=.opposite := by simp [role,noHS z zs,zh]
    rw [(backpair i ii z (mem_insert_of_mem zs)).2.1 (heads i ii) zr,
      (backpair j jj z (mem_insert_of_mem zs)).2.1 (heads j jj) zr]
  · have allS (x) (xs : x∈S) : X.D x h=true := by
      cases e : X.D x h with
      | true => rfl
      | false => exact False.elim (mixed ⟨x,xs,e⟩)
    have inRole (x) (xs : x∈S) := parent_role X hv (wv (cs.sub xs)) (allS x xs)
    have sends (t) (tt : t∈T) (tr : role X.D h t=.opposite) (x) (xs : x∈S) :=
      (backpair t tt x (mem_insert_of_mem xs)).2.2 tr (inRole x xs)
    have noST (x) (xs : x∈S) (t) (tt : t∈T) : X.D x t=false := by
      cases e : role X.D h t with
      | parent => exact False.elim (noTP t tt e)
      | opposite => exact Bool.eq_false_iff.mpr (digonfree X.free (by decide) (wv (tw tt)) (wv (cs.sub xs))
          (sends t tt e x xs))
      | head =>
        obtain ⟨z,zv,zh,op,tz⟩ := head_next X hv (wv (tw tt)) (head_arc e)
        have zt : z∈T := by
          apply mem_sdiff.mpr
          refine ⟨window z zv zh,?_⟩
          rintro zu
          rcases mem_union.mp zu with zp|zs
          · simp [formP z zp] at op
          · simp [inRole z zs] at op
        exact triangle (wv (tw tt)) zv (wv (cs.sub xs)) tz (sends z zt op x xs)
    apply forbids_module S cs.sub (by omega)
    intro x xs y ys z zv zs
    by_cases eq : z=h
    · subst z; rw [allS x xs,allS y ys]
    by_cases zt : z∈T
    · rw [noST x xs z zt,noST y ys z zt]
    have zp := (mem_union.mp (inside z (window z zv eq) zt)).resolve_right zs
    have pattern (i) (is' : i∈S) : X.D i z=true ↔ z=b := by
      refine ⟨fun iz => card_le_one.mp ((fits i is').heads i (mem_insert_self _ _)).le z
        (mem_outN.mpr ⟨mem_insert_of_mem zp,iz⟩) b (mem_outN.mpr ⟨mem_insert_of_mem bp,sb i is'⟩),
        fun eq => eq ▸ sb i is'⟩
    exact Bool.eq_iff_iff.mpr ((pattern x xs).trans (pattern y ys).symm)

/-- From the moving square S one or two general shared-head transitions
reach a retained square with a label outside the entire fixed path and S. -/
theorem packet_escape {n} (X : Model 3 n) {h a b P S} (hv : h∈X.V)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (large : 13≤X.V.card)
    (ps : P.card=3) (dis : Disjoint P S) (cs : Cycle X.D (X.V\{h}) 3 S)
    (fits : ∀x∈S,Cycle X.D (X.V\{h}) 3 (insert x P))
    (ap : a∈P) (bp : b∈P) (arcs : ∀x∈S,X.D a x=true ∧ X.D x b=true) :
    ∃A N t,(A=S ∨ PunctureCycleLoop.Step X.D S A) ∧ Cycle X.D (X.V\{h}) 3 A ∧
      PunctureCycleLoop.Step X.D A N ∧ Cycle X.D (X.V\{h}) 3 N ∧ t∈N ∧ t∉P∪S := by
  classical
  let W := X.V\{h}
  let T := W\(P∪S)
  have sz := cs.size
  obtain ⟨s,ss⟩ := card_pos.mp (by omega : 0<S.card)
  have pw : P⊆W := fun _ zp => (fits s ss).sub (mem_insert_of_mem zp)
  have wv : W⊆X.V := sdiff_subset
  have sub := union_subset pw cs.sub
  have he : h∈X.V\(P∪S) := mem_sdiff.mpr ⟨hv,fun hu => (mem_sdiff.mp (sub hu)).2 (mem_singleton_self h)⟩
  have back (x) : PunctureCycleLoop.Step X.D S (insert x P) := by
    have full : S⊆inN X.D S b := fun y ys => mem_inN.mpr ⟨ys,(arcs y ys).2⟩
    exact ⟨b,mem_sdiff.mpr ⟨mem_insert_of_mem bp,disjoint_left.mp dis bp⟩,(show 2≤S.card by omega).trans (card_le_card full)⟩
  by_cases stuck : ∀t∈T,(inN X.D P t).card+(inN X.D S t).card≤1
  · have allP := MinimumRootColumn.stalled_root X (by decide) wv ps dis cs fits he minimum large (by
      intro z zt
      obtain ⟨ne,ze⟩ := mem_erase.mp zt
      obtain ⟨zv,out⟩ := mem_sdiff.mp ze
      exact stuck z (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨zv,by simpa using ne⟩,out⟩))
    have total := card_sdiff_add_card_eq_card sub
    rw [card_union_of_disjoint dis,ps,sz] at total
    have ord := card_sdiff_add_card_eq_card (singleton_subset_iff.mpr hv)
    simp only [card_singleton] at ord
    have many : 2≤T.card := by dsimp [T,W] at *; omega
    obtain ⟨r,rr,t,tt,N,cn,rn,tn⟩ := root_bridge X hv ps cs fits bp (fun x xs => (arcs x xs).2) allP.1 many
    rcases mem_insert.mp rr with eq | rs
    · subst r
      exact ⟨S,N,t,Or.inl rfl,cs,⟨b,mem_sdiff.mpr ⟨rn,disjoint_left.mp dis bp⟩,
        (show 2≤S.card by omega).trans (card_le_card (show S⊆inN X.D S b from fun y ys => mem_inN.mpr ⟨ys,(arcs y ys).2⟩))⟩,
        cn,tn,(mem_sdiff.mp tt).2⟩
    · have one : (inN X.D S r).card=1 := cs.incoming r rs
      obtain ⟨y,yi⟩ := card_pos.mp (show 0<(inN X.D S r).card by omega)
      obtain ⟨ys,yr⟩ := mem_inN.mp yi
      have ry : r≠y := fun eq => loopfree X.free (by decide) (wv (cs.sub ys)) (eq ▸ yr)
      have ay : a≠y := fun eq => disjoint_left.mp dis ap (eq.symm ▸ ys)
      have out : r∉insert y P := fun z => (mem_insert.mp z).elim ry (fun rp => disjoint_left.mp dis rp rs)
      have rich := one_lt_card.mpr ⟨a,mem_inN.mpr ⟨mem_insert_of_mem ap,(arcs r rs).1⟩,y,
        mem_inN.mpr ⟨mem_insert_self y P,yr⟩,ay⟩
      exact ⟨insert y P,N,t,Or.inr (back y),fits y ys,⟨r,mem_sdiff.mpr ⟨rn,out⟩,rich⟩,cn,tn,(mem_sdiff.mp tt).2⟩
  · push Not at stuck
    obtain ⟨t,tt,high⟩ := stuck
    obtain ⟨N,cn,tn⟩ := PunctureCycleLoop.cover X large hv minimum (mem_sdiff.mp tt).1
    have out := (mem_sdiff.mp tt).2
    have ns : t∉S := fun ts => out (mem_union_right _ ts)
    have np : t∉P := fun tp => out (mem_union_left _ tp)
    by_cases both : 2≤(inN X.D S t).card
    · exact ⟨S,N,t,Or.inl rfl,cs,⟨t,mem_sdiff.mpr ⟨tn,ns⟩,both⟩,cn,tn,out⟩
    have lift (x) (xs : x∈S) (two : 2≤(inN X.D (insert x P) t).card) :
        PunctureCycleLoop.Step X.D (insert x P) N :=
      ⟨t,mem_sdiff.mpr ⟨tn,fun hh => (mem_insert.mp hh).elim (fun eq => ns (eq.symm ▸ xs)) np⟩,two⟩
    by_cases pp : 2≤(inN X.D P t).card
    · have inc : inN X.D P t⊆inN X.D (insert s P) t := fun y yi => mem_inN.mpr
          ⟨mem_insert_of_mem (mem_inN.mp yi).1,(mem_inN.mp yi).2⟩
      exact ⟨insert s P,N,t,Or.inr (back s),fits s ss,lift s ss (pp.trans (card_le_card inc)),cn,tn,out⟩
    obtain ⟨x,xi⟩ := card_pos.mp (show 0<(inN X.D S t).card by omega)
    obtain ⟨p,pi⟩ := card_pos.mp (show 0<(inN X.D P t).card by omega)
    obtain ⟨xs,xt⟩ := mem_inN.mp xi
    obtain ⟨pm,pt⟩ := mem_inN.mp pi
    have ne : p≠x := fun eq => disjoint_left.mp dis pm (eq.symm ▸ xs)
    have rich := one_lt_card.mpr ⟨p,mem_inN.mpr ⟨mem_insert_of_mem pm,pt⟩,x,
      mem_inN.mpr ⟨mem_insert_self x P,xt⟩,ne⟩
    exact ⟨insert x P,N,t,Or.inr (back x),fits x xs,lift x xs rich,cn,tn,out⟩

/-- Starting at an actual minimum-period shift orbit, a retained square
gains a label absent throughout that orbit. At most three general steps
are needed from the initial state, all in the same punctured graph. -/
theorem from_loop {n} (X : Model 3 n) {h} (hv : h∈X.V)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (large : 13≤X.V.card)
    (M : ℕ→Finset ℕ) (a u v b : ℕ→ℕ) (closed : M 4=M 0)
    (cycle : ∀i,Cycle X.D (X.V\{h}) 3 (M i))
    (move : ∀i,CycleSquareTensor.Shift X.D (M i) (M (i+1)) (a i) (u i) (v i) (b i)) :
    ∃S A N t,Cycle X.D (X.V\{h}) 3 S ∧ PunctureCycleLoop.Step X.D (M 0) S ∧
      (A=S ∨ PunctureCycleLoop.Step X.D S A) ∧ Cycle X.D (X.V\{h}) 3 A ∧
      PunctureCycleLoop.Step X.D A N ∧ Cycle X.D (X.V\{h}) 3 N ∧ t∈N ∧
      t∉S ∧ ∀i≤4,t∉M i := by
  classical
  let S := (range 4).image u
  let P := (M 0).erase (u 0)
  have safe := X.free.mono_set (sdiff_subset : X.V\{h}⊆X.V)
  obtain ⟨cs,_,_,_,arcs⟩ := AnchoredShiftFlow.least_period (by decide) safe M a u v b closed cycle move
  have us : u 0∈S := mem_image_of_mem u (mem_range.mpr (by decide))
  obtain ⟨dis,fits⟩ := ShortestCycleFiberModule.slots (by decide) safe (cycle 0)
    (move 0).aM (move 0).uM (move 0).bM cs.sub us arcs
  have ps : P.card=3 := by
    have e := card_erase_add_one (move 0).uM
    change P.card+1=(M 0).card at e
    rw [(cycle 0).size] at e
    omega
  have au : a 0≠u 0 := fun eq => loopfree safe (by decide) ((cycle 0).sub (move 0).uM) (eq ▸ (move 0).before₁)
  have bu : b 0≠u 0 := fun eq => loopfree safe (by decide) ((cycle 0).sub (move 0).uM) (eq ▸ (move 0).before₂)
  have ap : a 0∈P := mem_erase.mpr ⟨au,(move 0).aM⟩
  have bp : b 0∈P := mem_erase.mpr ⟨bu,(move 0).bM⟩
  obtain ⟨A,N,t,next,ca,last,cn,tn,fresh⟩ := packet_escape X hv minimum large ps dis cs fits ap bp arcs
  change t∉P∪S at fresh
  have same := (MarkedSquareFrontier.active_labels (by decide) safe M a u v b 4 (by decide) closed cycle move).1
  have vs (i) (hi : i<4) : v i∈S := by
    change v i∈(range 4).image u
    rw [same]; exact mem_image_of_mem v (mem_range.mpr hi)
  have start : PunctureCycleLoop.Step X.D (M 0) S :=
    ⟨v 0,mem_sdiff.mpr ⟨vs 0 (by decide),(move 0).exterior⟩,one_lt_card.mpr
      ⟨a 0,mem_inN.mpr ⟨(move 0).aM,(move 0).after₁⟩,u 0,mem_inN.mpr ⟨(move 0).uM,(move 0).move⟩,au⟩⟩
  have sub (i) (hi : i≤4) : M i⊆P∪S := by
    induction i with
    | zero =>
      intro x xm
      by_cases eq : x=u 0
      · exact mem_union_right _ (eq ▸ us)
      · exact mem_union_left _ (mem_erase.mpr ⟨eq,xm⟩)
    | succ i ih =>
      rw [(move i).labels]
      exact insert_subset (mem_union_right _ (vs i (by omega))) ((erase_subset _ _).trans (ih (by omega)))
  exact ⟨S,A,N,t,cs,start,next,ca,last,cn,tn,(fun ts => fresh (mem_union_right _ ts)),
    fun i hi tm => fresh (sub i hi tm)⟩

def EscapeLaw (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℕ) : Prop :=
  ∀h∈V,(∀z∈V,w h≤w z) → 13≤V.card → ∀(M : ℕ→Finset ℕ) (a u v b : ℕ→ℕ),
    M 4=M 0 → (∀i,Cycle D (V\{h}) 3 (M i)) →
    (∀i,CycleSquareTensor.Shift D (M i) (M (i+1)) (a i) (u i) (v i) (b i)) →
    ∃S A N t,Cycle D (V\{h}) 3 S ∧ PunctureCycleLoop.Step D (M 0) S ∧
      (A=S ∨ PunctureCycleLoop.Step D S A) ∧ Cycle D (V\{h}) 3 A ∧
      PunctureCycleLoop.Step D A N ∧ Cycle D (V\{h}) 3 N ∧ t∈N ∧
      t∉S ∧ ∀i≤4,t∉M i

theorem model_law {q n} (X : Model q n) : q=3 → EscapeLaw X.D X.V X.weights := by
  rintro rfl h hv minimum large M a u v b closed cycle move
  exact from_loop X hv minimum large M a u v b closed cycle move

#print axioms model_law
#print axioms from_loop
#print axioms packet_escape
#print axioms root_bridge
end LeanCH.BR.Closure.MinimumOrbitEscape
