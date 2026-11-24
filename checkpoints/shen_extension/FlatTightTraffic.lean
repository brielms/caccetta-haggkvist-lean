import checkpoints.shen_extension.FlatBankRectangle

namespace LeanCH.BR.Closure.FlatTightTraffic
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor FlatExchangeChain FlatExchangeTriangle FlatPairedExcursion
open FirstPacketBarrier MarkedCyclePeeling PairedFamilyLoop FlatBankRectangle

private def Entry (E : CH.Digraph) (V T : Finset ℕ) (h : ℕ) :=
  h∈V\T ∧ (inN E T h).Nonempty
private def ExitAt (E : CH.Digraph) (V T : Finset ℕ) (z : ℕ) :=
  z∈V\T ∧ (outN E T z).Nonempty
private def AtLevel (E : CH.Digraph) (V T : Finset ℕ) (m w i : ℕ) :=
  ∃h,Entry E V T h ∧ ∃z,ExitAt E V T z ∧ ∃j,i+j+1=m ∧
    Walk E (V\T) h w i ∧ Walk E (V\T) w z j

private theorem span_bound {E V T m h z w i j} (tv : T⊆V) (d : Delay E V T m)
    (he : Entry E V T h) (ze : ExitAt E V T z)
    (a : Walk E (V\T) h w i) (b : Walk E (V\T) w z j) : m ≤ (i + j + 1) := by
  obtain ⟨v,vh⟩ := ze.2
  obtain ⟨vt,edge⟩ := mem_outN.mp vh
  exact d h he.1 he.2 v vt _ (((a.append b).mono sdiff_subset).snoc (tv vt) edge)

private theorem unique_level {E V T m w i j} (tv : T⊆V) (d : Delay E V T m)
    (a : AtLevel E V T m w i) (b : AtLevel E V T m w j) : i=j := by
  obtain ⟨h,he,z,ze,k,eq,p,r⟩ := a
  obtain ⟨h',he',z',ze',l,eq',p',r'⟩ := b
  have x := span_bound tv d he ze' p r'
  have y := span_bound tv d he' ze p' r
  omega

private theorem start_level {E V T m h i} (tv : T⊆V) (d : Delay E V T m)
    (he : Entry E V T h) (a : AtLevel E V T m h i) : i=0 := by
  obtain ⟨_,_,z,ze,j,eq,_,r⟩ := a
  have := span_bound tv d he ze (.refl h) r
  omega

private theorem end_level {E V T m z i} (tv : T⊆V) (d : Delay E V T m)
    (ze : ExitAt E V T z) (a : AtLevel E V T m z i) : i+1=m := by
  obtain ⟨h,he,_,_,j,eq,p,_⟩ := a
  have := span_bound tv d he ze p (.refl z)
  omega

private theorem forward {E L f i j} (path : Chain E L f) (ij : i≤j) (jm : j<L.card) :
    Walk E L (f i) (f j) (j-i) := by
  apply walk_between (m:=j) _ ij le_rfl
  intro k hk
  exact ⟨path.mem (by omega),(path.edge k (by omega) _ (by omega)).mpr rfl⟩

/-- The position along a tight exterior interval supplies both walks on the same cycle. -/
private theorem chain_levels {E V T q N m f} (cn : Cycle E V q N) (p : Chain E (N\T) f)
    (size : (N\T).card=m) (pos : 0<m) :
    ∀i<m,AtLevel E V T m (f i) i := by
  let L := N\T
  have lift : L⊆V\T := fun v vh => mem_sdiff.mpr ⟨cn.sub (mem_sdiff.mp vh).1,(mem_sdiff.mp vh).2⟩
  have st := p.mem (show 0<(N\T).card by omega)
  have en := p.mem (show m-1<(N\T).card by omega)
  have fs := (mem_sdiff.mp st).1
  have fe := (mem_sdiff.mp en).1
  obtain ⟨a,ah⟩ := card_pos.mp (show 0<(inN E N (f 0)).card by rw [show (inN E N (f 0)).card=1 from cn.incoming _ fs]; decide)
  obtain ⟨an,arc⟩ := mem_inN.mp ah
  have atc : a∈T := by
    by_contra no
    obtain ⟨k,hk,rfl⟩ := p.index (mem_sdiff.mpr ⟨an,no⟩)
    have := (p.edge k hk 0 (by omega)).mp arc
    omega
  obtain ⟨b,bh⟩ := card_pos.mp (show 0<(outN E N (f (m-1))).card by rw [cn.heads _ fe]; decide)
  obtain ⟨bn,edge⟩ := mem_outN.mp bh
  have bt : b∈T := by
    by_contra no
    obtain ⟨k,hk,rfl⟩ := p.index (mem_sdiff.mpr ⟨bn,no⟩)
    have := (p.edge (m-1) (by omega) k hk).mp edge
    omega
  intro i hi
  refine ⟨_,⟨lift st,a,mem_inN.mpr ⟨atc,arc⟩⟩,_,⟨lift en,b,mem_outN.mpr ⟨bt,edge⟩⟩,m-1-i,by omega,?_,?_⟩
  · simpa using (forward p (Nat.zero_le i) (by omega)).mono lift
  · exact (forward p (show i≤m-1 by omega) (by omega)).mono lift

/-- First return to the interior, with the exact exterior prefix retained. -/
private theorem entrance {E V T h t k} (w : Walk E V h t k) (hw : h∈V\T) (tt : t∈T) :
    ∃z,ExitAt E V T z ∧ ∃v∈T,∃r l,r+1+l=k ∧ Walk E (V\T) h z r ∧
      v∈V ∧ E z v=true ∧ Walk E V v t l := by
  induction w with
  | refl => exact ((mem_sdiff.mp hw).2 tt).elim
  | @step a b t k bv edge tail ih =>
    by_cases bt : b∈T
    · exact ⟨a,⟨hw,b,mem_outN.mpr ⟨bt,edge⟩⟩,b,bt,0,k,by omega,.refl _,bv,edge,tail⟩
    · obtain ⟨z,ze,v,vt,r,l,sz,p,vv,e,rst⟩ := ih (mem_sdiff.mpr ⟨bv,bt⟩) tt
      exact ⟨z,ze,v,vt,r+1,l,by omega,.step (mem_sdiff.mpr ⟨bv,bt⟩) edge p,vv,e,rst⟩

/-- If every crossing used the minimum exterior length, all exterior arcs would
advance one common level. Saturation would then make every entry have the same
incoming column. The singleton entry contradicts avoidance of individual labels. -/
theorem long_cycle {D F V T q m} (hq : 1≤q) (bal : q+1=2*m) (tv : T⊆V)
    (free : QFree (graph D F) V q) (sat : BRsub.Sat q (graph D F) V)
    (cycles : ∀I∈F,Cycle (graph D F) V q I) (delay : Delay (graph D F) V T m)
    (sep : ∀u∈V,∀v∈V,(∀w∈V,graph D F w u=true → graph D F w v=true) → u=v)
    (live : (V\T).Nonempty) (avoid : ∀z∈V\T,∃N∈F,(N\T).Nonempty ∧ z∉N) :
    ∃N∈F,m<(N\T).card := by
  classical
  let E := graph D F
  let W := V\T
  by_contra! cap
  have mp : 0<m := by omega
  have chains (N) (nf : N∈F) (extN : (N\T).Nonempty) :
      ∃f,Chain E (N\T) f ∧ (N\T).card=m ∧ ∀i<m,AtLevel E V T m (f i) i := by
    have cn := cycles N nf
    have sp := card_sdiff_add_card_inter N T
    rw [cn.size] at sp
    have lim := cap N nf
    have ins : (N∩T).Nonempty := card_pos.mp (by omega)
    obtain ⟨lo,⟨f,path⟩,_⟩ := outside_interval free cn bal.le delay ins extN
    exact ⟨f,path,by omega,chain_levels cn path (by omega) mp⟩
  have wit {u v} (arc : E u v=true) : ∃N∈F,u∈N ∧ v∈N := by
    obtain ⟨N,nh⟩ := active.mp arc
    obtain ⟨nf,un,vn,_⟩ := mem_col.mp nh
    exact ⟨N,nf,un,vn⟩
  have advance {u v} (uw : u∈W) (vw : v∈W) (edge : E u v=true) :
      ∃i,AtLevel E V T m u i ∧ AtLevel E V T m v (i+1) := by
    obtain ⟨N,nf,un,vn⟩ := wit edge
    have outside := mem_sdiff.mpr ⟨un,(mem_sdiff.mp uw).2⟩
    obtain ⟨f,path,sz,lev⟩ := chains N nf ⟨u,outside⟩
    obtain ⟨i,hi,rfl⟩ := path.index outside
    obtain ⟨j,hj,rfl⟩ := path.index (mem_sdiff.mpr ⟨vn,(mem_sdiff.mp vw).2⟩)
    have eq := (path.edge i hi j hj).mp edge
    exact ⟨i,lev i (by omega),eq ▸ lev j (by omega)⟩
  have root {h} (he : Entry E V T h) : AtLevel E V T m h 0 := by
    obtain ⟨t,th⟩ := he.2
    obtain ⟨N,nf,_,hn⟩ := wit (mem_inN.mp th).2
    have outside := mem_sdiff.mpr ⟨hn,(mem_sdiff.mp he.1).2⟩
    obtain ⟨f,path,sz,lev⟩ := chains N nf ⟨h,outside⟩
    obtain ⟨i,hi,eq⟩ := path.index outside
    have ai : AtLevel E V T m h i := eq ▸ lev i (by omega)
    exact start_level tv delay he ai ▸ ai
  have follow {h z k} (p : Walk E W h z k) (hw : h∈W) (i) (ai : AtLevel E V T m h i) :
      AtLevel E V T m z (i+k) := by
    induction p generalizing i with
    | refl => exact ai
    | step bv edge _ ih =>
      obtain ⟨j,aj,an⟩ := advance hw bv edge
      obtain rfl := unique_level tv delay ai aj
      simpa only [Nat.add_assoc,Nat.add_comm 1] using ih bv (_+1) an
  have lengths {h z k} (he : Entry E V T h) (ze : ExitAt E V T z) (p : Walk E W h z k) : k+1=m := by
    have := end_level tv delay ze (follow p he.1 0 (root he))
    omega
  have none : ¬∃N∈F,N⊆W := by
    rintro ⟨N,nf,nw⟩
    have eq : N\T=N := by
      apply Subset.antisymm sdiff_subset
      intro x xn
      exact mem_sdiff.mpr ⟨xn,(mem_sdiff.mp (nw xn)).2⟩
    have lim := cap N nf
    rw [eq,(cycles N nf).size] at lim
    omega
  have connect {h z} (he : Entry E V T h) (ze : ExitAt E V T z) :
      ∃k,Walk E W h z k := by
    have cut : FlatReturnLayers.Cuts E V T W := fun h hw _ miss => (miss hw).elim
    obtain ⟨_,_,r,l,_,_,a,b⟩ := rectangle hq bal tv free sat cycles delay none cut he.1 he.2 ze.1 ze.2
    exact ⟨r+l,a.append b⟩
  have equal {h g} (he : Entry E V T h) (ge : Entry E V T g) : h=g := by
    apply sep h (mem_sdiff.mp he.1).1 g (mem_sdiff.mp ge.1).1
    intro u uv edge
    by_cases ut : u∈T
    · by_contra miss
      obtain ⟨_,k,le,w⟩ := mem_ball.mp (sat g (mem_sdiff.mp ge.1).1 u uv miss)
      obtain ⟨z,ze,v,_,r,l,eq,p,vv,back,tail⟩ := entrance w ge.1 ut
      obtain ⟨r',p'⟩ := connect he ze
      have lr := lengths ge ze p
      have lr' := lengths he ze p'
      have route := (((p'.mono sdiff_subset).snoc vv back).append tail).snoc (mem_sdiff.mp he.1).1 edge
      exact free h _ (by omega) (by omega) route
    · obtain ⟨j,_,hi⟩ := advance (mem_sdiff.mpr ⟨uv,ut⟩) he.1 edge
      have := start_level tv delay he hi
      omega
  obtain ⟨w,ww⟩ := live
  obtain ⟨M,mf,extM,_⟩ := avoid w ww
  obtain ⟨f,_,_,lev⟩ := chains M mf extM
  obtain ⟨h,he,_⟩ := lev 0 mp
  obtain ⟨N,nf,extN,miss⟩ := avoid h he.1
  obtain ⟨g,path,sz,lev'⟩ := chains N nf extN
  obtain ⟨u,ue,_,_,_,_,w0,_⟩ := lev' 0 mp
  have eq : u=g 0 := by cases w0; rfl
  exact miss (equal he ue ▸ eq.symm ▸ (mem_sdiff.mp (path.mem (by omega : 0<(N\T).card))).1)

#print axioms long_cycle

theorem on_schedule {q D V F} (hq : 2≤q) (free : QFree (graph D F) V q)
    (small : SmallerSmallRow q V.card) (cycles : ∀I∈F,Cycle (graph D F) V q I)
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (mark : ∀s,Marked (graph D F) (previous s) (current s) (current (go s)))
    (flat : ∀a : Function.periodicPts go,BRsub.Sat q (graph D F) (V\RawRepairAlternative.gone a.val))
    {x p : ℕ→ℚ} (xp : ∀u∈V,0<x u) (pp : ∀u∈V,0≤p u)
    (strict : ∀u∈V,mass V x<WeightedSD.row q (graph D F) V x u)
    (costrict : ∀u∈V,mass V p<WeightedSD.col q (graph D F) V p u)
    (s : Function.periodicPts go) :
    let E := graph D F
    let A := previous s.val
    let B := current s.val
    let C := current (go s.val)
    let T := A∪B∪C
    ((V\RawRepairAlternative.gone s.val).card : ZMod q)=1 →
    Packet E V A B C →
    Packet E V (previous (go s.val)) C (current (go (go s.val))) →
    Packet E V (previous (go (go s.val))) (current (go (go s.val))) (current (go (go (go s.val)))) →
    (∃N∈F,(B\C).card<(N\T).card) ∧
      ((∃N∈F,N⊆V\T) ∨ ∃S⊆V\T,(B\C).card*S.card≤(V\T).card ∧
        ∀h∈V\T,(inN E T h).Nonempty → ∀z∈V\T,(outN E T z).Nonempty →
          ∃w∈S,∃r l,(B\C).card≤r+l+1 ∧ r+l<q ∧ Walk E (V\T) h w r ∧ Walk E (V\T) w z l) := by
  classical
  intro E A B C T modOne a b c
  obtain ⟨⟨k,kl,eq⟩,avoids⟩ := FlatMinimumExterior.on_schedule hq free small cycles go join mark flat xp pp strict costrict s modOne a b c
  have left (v : PairedFamilyLoop.State F) := cycles _ (mem_product.mp (mem_filter.mp v.property).1).1
  have right (v : PairedFamilyLoop.State F) := cycles _ (mem_product.mp (mem_filter.mp v.property).1).2
  have period := period_three free go left right join mark s.val a b c
  have odd : ¬Even (Function.minimalPeriod go s.val) := by rw [period]; decide
  have sat := FlatOrbitSaturation.odd_saturated go join flat s odd
  have ret (v : PairedFamilyLoop.State F) := scheduled_return free (left v) (right v) (right (go v))
    (right (go (go v))) (join v) (mark v) (mark (go v))
  have next := ret s.val a b
  have afterNext := ret (go s.val) b c
  dsimp only [A,B,C,E] at a b c
  rw [join s.val,next] at b
  rw [join (go s.val),next,afterNext,join s.val] at c
  have ca : Cycle E V q A := left s.val
  have cb : Cycle E V q B := right s.val
  have cc : Cycle E V q C := right (go s.val)
  have tv : T⊆V := union_subset (union_subset ca.sub cb.sub) cc.sub
  have bal : q+1=2*(B\C).card := by
    obtain ⟨e⟩ := a.copy
    have cnt : (B\C).card=(A\B).card := by simpa only [Fintype.card_coe] using Fintype.card_congr e.equiv
    have x := card_sdiff_add_card_inter A B
    rw [ca.size,show A∩B=B\C from a.overlap,←cnt] at x
    omega
  have de := triple_exit free ca cb cc a b c
  change (V\T).card=q*k at eq
  have positive : 0<(V\T).card := eq ▸ Nat.mul_pos (by omega) (by omega)
  constructor
  · refine long_cycle (by omega) bal tv free sat cycles de ?_ (card_pos.mp positive) ?_
    · intro u uv v vv dom
      by_contra ne
      exact strict_no_incoming_domination (small.induced free) x (fun i hi => (xp i hi).le) strict uv vv ne
        (fun w wh => dom w (mem_of_mem_erase wh))
    · intro z zw
      obtain ⟨N,nf,far,absent,_⟩ := avoids z zw
      exact ⟨N,nf,far,absent⟩
  · by_cases extN : ∃N∈F,N⊆V\T
    · exact Or.inl extN
    · obtain ⟨S,sub,cap,cut⟩ := FlatReturnLayers.thin free ca cb cc a b c
      exact Or.inr ⟨S,sub,cap,fun _ hw ins _ zw out =>
        rectangle (by omega) bal tv free sat cycles de extN cut hw ins zw out⟩

#print axioms on_schedule

end LeanCH.BR.Closure.FlatTightTraffic
