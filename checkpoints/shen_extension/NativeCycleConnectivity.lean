import checkpoints.shen_extension.SharedArcGrid

namespace LeanCH.BR.Closure.NativeCycleConnectivity
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open SharedArcExpansion SharedArcGrid

private theorem mf_of {q n} {X : Model q n} {M} (cm : Cycle X.D X.V q M) : M∈family X := by
  classical exact mem_filter.mpr ⟨mem_powerset.mpr cm.sub,cm⟩

private theorem cycle_of {q n} {X : Model q n} {M} (mf : M∈family X) : Cycle X.D X.V q M := by
  classical exact (mem_filter.mp mf).2

private theorem neighbours {D V q M h} (hq : 2≤q) (free : QFree D V q) (cm : Cycle D V q M) (hm : h∈M) :
    ∃p∈M,∃t∈M,D p h=true ∧ D h t=true ∧ ¬D p t=true := by
  obtain ⟨p,pm⟩ := card_pos.mp (show 0<(inN D M h).card by rw [show (inN D M h).card=1 from cm.incoming h hm]; decide)
  obtain ⟨t,tm⟩ := card_pos.mp (show 0<(outN D M h).card by rw [cm.heads h hm]; decide)
  obtain ⟨pc,ph⟩ := mem_inN.mp pm
  obtain ⟨tc,ht⟩ := mem_outN.mp tm
  refine ⟨p,pc,t,tc,ph,ht,fun pt => ?_⟩
  obtain rfl : t=h := card_le_one.mp (cm.heads p pc).le _ (mem_outN.mpr ⟨tc,pt⟩) _ (mem_outN.mpr ⟨hm,ph⟩)
  exact loopfree free (by omega : 1≤q) (cm.sub tc) ht

private def Sandwich (D : CH.Digraph) (col : Color) (p t : ℕ) (B : Finset ℕ) :=
  ∀z∈B,(D p z=true ∧ col p z) ∧ (D z t=true ∧ col z t)

/-- A blue cycle cannot be placed between two red vertices this way.
The same two red endpoints would surround every blue cycle reached by a
shared arc, including one through the first endpoint. -/
private theorem outer_false {q n} (X : Model q n) (hq : 2≤q) {col : Color} (sw : Switch X.D X.V col)
    (mono : ∀A∈family X,HasColor X.D A col ∨ HasColor X.D A (other col))
    {p t B} (pv : p∈X.V) (tv : t∈X.V) (miss : ¬X.D p t=true)
    (bf : B∈family X) (blue : HasColor X.D B (other col)) (start : Sandwich X.D col p t B) : False := by
  classical
  have pass {A N} (af : A∈family X) (nf : N∈family X) (ab : HasColor X.D A (other col))
      (outer : Sandwich X.D col p t A) (touch : Touch X.D A N) :
      HasColor X.D N (other col) ∧ Sandwich X.D col p t N := by
    obtain ⟨z,iz,w,iw,zw⟩ := touch
    obtain ⟨za,zn⟩ := mem_inter.mp iz
    obtain ⟨wa,wn⟩ := mem_inter.mp iw
    have nb : HasColor X.D N (other col) :=
      (mono N nf).resolve_left (fun red => ab z za w wa zw (red z zn w wn zw))
    have cN := cycle_of nf
    have replaceAt (u) (ua : u∈A) : ∃T,Cycle X.D X.V q T ∧ p∈T ∧ u∈T ∧ t∈T ∧ HasColor X.D T col := by
      have pay := outer u ua
      obtain ⟨T,ct,pt,ut,tt⟩ := SaturatedCycleClasses.missing hq X.free X.sat pv ((cycle_of af).sub ua) tv pay.1.1 pay.2.1 miss
      exact ⟨T,ct,pt,ut,tt,(mono T (mf_of ct)).resolve_right (fun blue => blue p pt u ut pay.1.1 pay.1.2)⟩
    obtain ⟨T,ct,pt,zt,_,red⟩ := replaceAt z za
    have left := (corner hq X.free sw ct cN red nb zt zn pt wn (outer z za).1.1 zw).resolve_right
      (fun all => (all p pt).2 (outer w wa).1.2)
    obtain ⟨U,cu,_,wu,tu,redU⟩ := replaceAt w wa
    have right := (corner hq X.free.reverse sw.rev (reverse_cycle cu) (reverse_cycle cN) redU.rev nb.rev
      wu wn tu zn (outer w wa).2.1 zw).resolve_right (fun all => (all t tu).2 (outer z za).2.2)
    exact ⟨nb,fun u un => ⟨left u un,right u un⟩⟩
  have all {F} (built : Built X.D B F) (sub : F⊆family X) :
      ∀A∈F,HasColor X.D A (other col) ∧ Sandwich X.D col p t A := by
    induction built with
    | seed => simpa using And.intro blue start
    | @add F A N _ af touch _ ih =>
      have old := ih ((subset_insert N F).trans sub)
      intro M mf
      rcases mem_insert.mp mf with rfl|inF
      · exact pass (sub (mem_insert_of_mem af)) (sub (mem_insert_self _ _)) (old A af).1 (old A af).2 touch
      · exact old _ inF
  obtain ⟨F,_,chain,sub,cover,_⟩ := span_all X hq (Built.seed : Built X.D B {B}) (singleton_subset_iff.mpr bf)
  obtain ⟨A,af,pa⟩ := mem_biUnion.mp (cover.symm ▸ pv : p∈support F)
  exact loopfree X.free (by omega : 1≤q) pv ((all chain sub A af).2 p pa).1.1

/-- A coloring constant on each shortest cycle, in which color changes force
shortcuts, cannot have a red cycle and a blue cycle through the same vertex. -/
theorem no_mixed_vertex {q n} (X : Model q n) (hq : 2≤q) {col : Color} (sw : Switch X.D X.V col)
    (mono : ∀A∈family X,HasColor X.D A col ∨ HasColor X.D A (other col))
    {C B h} (cf : C∈family X) (bf : B∈family X) (hc : h∈C) (hb : h∈B)
    (red : HasColor X.D C col) (blue : HasColor X.D B (other col)) : False := by
  have cc := cycle_of cf
  have cb := cycle_of bf
  obtain ⟨p,pc,t,tc,ph,ht,pt⟩ := neighbours hq X.free cc hc
  obtain ⟨r,rb,s,sb,rh,hs,rs⟩ := neighbours hq X.free cb hb
  have go := corner hq X.free sw cc cb red blue hc hb pc sb ph hs
  have back := corner hq X.free.reverse sw.rev (reverse_cycle cc) (reverse_cycle cb) red.rev blue.rev hc hb tc rb ht rh
  rcases go with left|right <;> rcases back with down|up
  · exact outer_false X hq sw mono (cc.sub pc) (cc.sub tc) pt bf blue (fun u ub => ⟨left u ub,down u ub⟩)
  · exact X.free p 2 (by omega) hq (.step (cb.sub rb) (left r rb).1 (.step (cc.sub pc) (up p pc).1 (.refl _)))
  · exact X.free t 2 (by omega) hq (.step (cb.sub sb) (right t tc).1 (.step (cc.sub tc) (down s sb).1 (.refl _)))
  · have twice {A} (redA : HasColor X.D A col) : HasColor X.D A (other (other col)) :=
      fun i ia j ja edge no => no (redA i ia j ja edge)
    have mono' (A) (af : A∈family X) := (mono A af).elim (fun cr => Or.inr (twice cr)) Or.inl
    exact outer_false X hq sw.other mono' (cb.sub rb) (cb.sub sb) rs cf (twice red)
      (fun u uc => ⟨up u uc,right u uc⟩)

/-- The entire native shortest-cycle family is connected by transitions
sharing a directed arc. This holds at every cutoff and for every order. -/
theorem connected {q n} (X : Model q n) (hq : 2≤q) {C B} (cf : C∈family X) (bf : B∈family X) :
    Linked X C B := by
  classical
  let col : Color := fun u v => ∃A∈family X,Linked X C A ∧ u∈A ∧ v∈A
  have colors (A) (af : A∈family X) : (Linked X C A → HasColor X.D A col) ∧
      (¬Linked X C A → HasColor X.D A (other col)) := by
    refine ⟨fun reach i ia j ja _ => ⟨A,af,reach,ia,ja⟩,?_⟩
    rintro no i ia j ja edge ⟨M,mf,cm,im,jm⟩
    exact no (.trans _ _ _ cm (.rel _ _ ⟨mf,af,i,mem_inter.mpr ⟨im,ia⟩,j,mem_inter.mpr ⟨jm,ja⟩,edge⟩))
  have mono (A) (af : A∈family X) : HasColor X.D A col ∨ HasColor X.D A (other col) := by
    by_cases c : Linked X C A
    · exact Or.inl ((colors A af).1 c)
    · exact Or.inr ((colors A af).2 c)
  have sw : Switch X.D X.V col := by
    intro u uv v vv w wv a b diff
    by_contra no
    obtain ⟨M,cm,um,vm,wm⟩ := SaturatedCycleClasses.missing hq X.free X.sat uv vv wv a b no
    rcases mono M (mf_of cm) with m|m
    · exact diff ⟨fun _ => m v vm w wm b,fun _ => m u um v vm a⟩
    · exact diff ⟨fun e => (m u um v vm a e).elim,fun e => (m v vm w wm b e).elim⟩
  by_contra no
  have cc := cycle_of cf
  obtain ⟨h,hc⟩ := card_pos.mp (show 0<C.card by rw [cc.size]; omega)
  obtain ⟨M,mf,bm,hm⟩ := reaches_vertex X hq bf (cc.sub hc)
  have ncm : ¬Linked X C M := fun cm => no (.trans _ _ _ cm (.symm _ _ bm))
  exact no_mixed_vertex X hq sw mono cf mf hc hm ((colors C cf).1 (.refl _)) ((colors M mf).2 ncm)

#print axioms no_mixed_vertex
#print axioms connected
end LeanCH.BR.Closure.NativeCycleConnectivity
