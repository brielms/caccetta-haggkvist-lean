import checkpoints.shen_extension.OneSpareCycleBudget
import checkpoints.shen_extension.SinkTransit
namespace LeanCH.BR.SparseCycleReturns
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- After entering a row from a shortest cycle, at most k+1 cycle labels
can be reached back by radius k. -/
theorem reached_cap {D V C T q k a c} (free : QFree D V q) (cv : C⊆V)
    (size : C.card=q+1) (one : OutEq 1 D C) (cm : c∈C) (av : a∈V)
    (entry : D c a=true) (tc : T⊆C) (reach : T⊆ball D V a k) (time : k+1≤q) :
    T.card≤k+1 := by
  let B := ball (fun x y=>D y x) C c (q-k-1)
  have rev := (dt_reg (by omega : 1≤q) (ball_q_one q (by omega))
    (free.mono_set cv) (fun x xm=>(one x xm).ge) (by simpa using size)).2
  have grow := ball_one_growth (free.mono_set cv).reverse (fun x xm=>(rev x xm).ge) cm (q-k-1) (by omega)
  change q-k-1+1≤B.card at grow
  have dis : Disjoint T B := by
    apply disjoint_left.mpr
    intro b bm back
    obtain ⟨_,i,le,fwd⟩ := mem_ball.mp (reach bm)
    obtain ⟨_,j,le',revwalk⟩ := mem_ball.mp back
    exact free c _ (by omega) (by omega) (.step av entry (fwd.append ((revwalk.reverse_of_mem cm).mono cv)))
  have cap := card_le_card (union_subset tc (show B⊆C from ball_subset))
  rw [card_union_of_disjoint dis] at cap
  omega

/-- If the second shell is itself a shortest cycle, a return into the
first shell would put an entire sink row back on the cycle in at most
three steps. The cycle has room for at most four such labels. -/
theorem cyclic_second_no_return {D V X Y q r} (free : QFree D V q)
    (xv : X⊆V) (yv : Y⊆V) (xy : Disjoint X Y) (dx : X.card=r)
    (dy : Y.card=q+1) (one : OutEq 1 D Y) (time : r≤q) (hr : 5≤r)
    (rank : ∀x∈X,r≤(outN D (X∪Y) x).card) :
    ∀y∈Y,∀x∈X,D y x≠true := by
  intro y ym x xm entry
  have direct := reached_cap free yv dy one ym (xv xm) entry outN_subset
    (show outN D Y x⊆ball D V x 1 from fun a am=>ball_of_adj (yv (outN_subset am)) (mem_outN.mp am).2)
    (by omega)
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set xv) (show X.card≤q by omega) xm
  have depth := SinkTransit.internal_depth (free.mono_set xv) (show X.card≤q by omega) p
  have total := rank x xm
  rw [card_outN_union xy] at total
  have near : p.len≤2 := by omega
  let s := p.vertex p.len
  have sx : s∈X := p.mem _ le_rfl
  have empty : outN D X s=∅ := eq_empty_iff_forall_notMem.mpr
    (fun a am=>p.sink a (outN_subset am) (mem_outN.mp am).2)
  have full := rank s sx
  rw [card_outN_union xy,empty,card_empty,zero_add] at full
  have walk : Walk D X x s p.len := by
    simpa only [p.start,Nat.sub_zero] using p.walk (Nat.zero_le _) le_rfl
  have via : outN D Y s⊆ball D V x 3 := by
    intro a am
    exact mem_ball.mpr ⟨yv (outN_subset am),_,by omega,(walk.mono xv).snoc (yv (outN_subset am)) (mem_outN.mp am).2⟩
  have := reached_cap free yv dy one ym (xv xm) entry outN_subset via (by omega)
  omega

/-- On four successive BFS layers, two consecutive deficient outer
shells are impossible when the actual second layer fits the one-spare
shortest-cycle bound. No assumption about cycles in that layer is needed. -/
theorem two_deficient {D V q r u} (free : QFree D V q) (root : u∈V)
    (degree : ∀v∈V,r≤(outN D V v).card) (row : (outN D V u).card=r)
    (hr : 7≤r) (time : r≤q) (width : (N2 D V u).card≤q+1)
    (narrow : (N3 D V u).card<r) : r≤(ball D V u 4\ball D V u 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4\ball D V u 3
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have xy : Disjoint X Y := disjXY
  have dx : X.card=r := row
  have cut := free.mono_bound (show 4≤q by omega)
  have keep x (xm : x∈X) : r≤(outN D (X∪Y) x).card := by rw [←outN_X_eq cut root xm]; exact degree x (xv xm)
  have split : (X∪Y)\X=Y := by ext a; simp only [mem_sdiff,mem_union]; constructor <;> grind [disjoint_left.mp xy]
  have sz := card_union_of_disjoint xy
  have cy : ¬QFree D Y Y.card := by
    intro off
    have ff := free.mono_set (union_subset xv yv)
    have pos v (vm : v∈X∪Y) : 1≤(outN D (X∪Y) v).card := by
      rcases mem_union.mp vm with vx|vy
      · exact (show 1≤r by omega).trans (keep v vx)
      · have sub : outN D V v⊆outN D (X∪Y) v ∪ Z := by
          intro a am
          rcases headY cut root vy (outN_subset am) (mem_outN.mp am).2 with h|h
          · exact mem_union_left _ (mem_outN.mpr ⟨h,(mem_outN.mp am).2⟩)
          · exact mem_union_right _ h
        have h := (card_le_card sub).trans (card_union_le _ _)
        have := degree v (yv vy)
        change Z.card<r at narrow
        omega
    have cap := one_spare ff (by omega) (subset_union_left : X⊆X∪Y) pos keep (by omega) time
      (by change Y.card≤q+1 at width; omega) (by rwa [split])
    omega
  have greater : q<Y.card := by
    by_contra! short
    exact cy ((free.mono_set yv).mono_bound short)
  have dy : Y.card=q+1 := by change Y.card≤q+1 at width; omega
  have all : ∀y∈Y,1≤(outN D Y y).card := by
    unfold QFree at cy
    push Not at cy
    obtain ⟨a,k,pos,le,walk⟩ := cy
    have eq : k=q+1 := by
      by_contra h
      exact (free.mono_set yv) a k pos (by omega) walk
    subst k
    obtain ⟨C,sub,cardC,paid⟩ := boundary_closed_walk_support (free.mono_set yv) walk
    exact eq_of_subset_of_card_le sub (by omega) ▸ paid
  have one := EqualShellEscape.one_head (free.mono_set yv) (by omega) (show Y.card≤q+1 by omega) all
  have back := cyclic_second_no_return free xv yv xy dx dy one time (by omega) keep
  have full y (ym : y∈Y) : Z⊆outN D V y := by
    have part : outN D V y⊆outN D Y y∪outN D Z y := by
      intro a am
      have edge := (mem_outN.mp am).2
      rcases headY cut root ym (outN_subset am) edge with h|h
      · have ay := (mem_union.mp h).resolve_left (fun ax=>back y ym a ax edge)
        exact mem_union_left _ (mem_outN.mpr ⟨ay,edge⟩)
      · exact mem_union_right _ (mem_outN.mpr ⟨h,edge⟩)
    have count := (card_le_card part).trans (card_union_le _ _)
    rw [one y ym] at count
    have := degree y (yv ym)
    change Z.card<r at narrow
    have eq : outN D Z y=Z := eq_of_subset_of_card_le outN_subset (by omega)
    exact eq ▸ (outN_mono zv y : outN D Z y⊆outN D V y)
  have first x (xm : x∈X) : (outN D Y x).Nonempty := by
    have sub : outN D X x⊆X.erase x := fun a am=>mem_erase.mpr ⟨fun eq=>loopfree free (by omega) (xv xm) (eq ▸ (mem_outN.mp am).2),outN_subset am⟩
    have cap := card_le_card sub
    rw [card_erase_of_mem xm] at cap
    have h := keep x xm
    rw [card_outN_union xy] at h
    exact card_pos.mp (by omega)
  have nz : Z.Nonempty := by
    obtain ⟨y,ym⟩ := card_pos.mp (by omega : 0<Y.card)
    have x := degree y (yv ym)
    have sub : outN D V y⊆outN D Y y∪Z := fun a am=>by
      rcases headY cut root ym (outN_subset am) (mem_outN.mp am).2 with h|h
      · exact mem_union_left _ (mem_outN.mpr ⟨(mem_union.mp h).resolve_left (fun ax=>back y ym a ax (mem_outN.mp am).2),(mem_outN.mp am).2⟩)
      · exact mem_union_right _ h
    have count := (card_le_card sub).trans (card_union_le _ _)
    rw [one y ym] at count
    exact card_pos.mp (by omega)
  obtain ⟨z,zm,sink⟩ := exists_sink (free.mono_set zv) nz (by change Z.card<r at narrow; omega)
  have out : outN D V z⊆W := by
    intro a am
    have arc := (mem_outN.mp am).2
    rcases split4 (E:=D) root a with eq|ax|ay|az|far
    · exact (no_back_arc free root (mem_N3.mp zm).1 (by omega) (eq ▸ arc)).elim
    · obtain ⟨y,ym⟩ := first a ax
      have seen := ball_step (ball_of_adj (yv (outN_subset ym)) (mem_outN.mp ym).2) (zv zm) (mem_outN.mp (full y (outN_subset ym) zm)).2
      exact (no_back_arc free (xv ax) seen (by omega) arc).elim
    · exact (no_back_arc free (yv ay) (ball_of_adj (zv zm) (mem_outN.mp (full a ay zm)).2) (by omega) arc).elim
    · exact (sink a az arc).elim
    · exact mem_sdiff.mpr ⟨ball_step (mem_N3.mp zm).1 (outN_subset am) arc,far⟩
  exact (degree z (zv zm)).trans (card_le_card out)

attribute [aesop safe forward (immediate := [free,cv,size,one,cm,av,entry,tc,reach,time]) (rule_sets := [CHGraphFamilies])] reached_cap
attribute [aesop safe forward (immediate := [free,xv,yv,xy,dx,dy,one,time,hr,rank]) (rule_sets := [CHGraphFamilies])] cyclic_second_no_return
attribute [aesop safe forward (immediate := [free,root,degree,row,hr,time,width,narrow]) (rule_sets := [CHGraphFamilies])] two_deficient
#print axioms reached_cap
#print axioms cyclic_second_no_return
#print axioms two_deficient
end LeanCH.BR.SparseCycleReturns
