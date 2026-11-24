import checkpoints.shen_extension.PhysicalCycleStockWitnessReplay
import checkpoints.shen_extension.SinkDepthCover

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- A shortest internal positive walk gives a single induced cycle on the
same labels, with a return path inside it from every root. -/
theorem actual_cycle {D V W q} (free : QFree D V q) (hq : 1≤q) (wv : W⊆V)
    (cyclic : ¬QFree D W W.card) :
    ∃C⊆W,q<C.card ∧ ∀v∈C,Rooted D V v C := by
  classical
  unfold QFree at cyclic
  push Not at cyclic
  obtain ⟨a,m,hm,_,w⟩ := cyclic
  have existsLength : ∃k,∃a,0<k ∧ Walk D W a a k := ⟨m,a,hm,w⟩
  obtain ⟨a,pos,walk⟩ := Nat.find_spec existsLength
  have long : q<Nat.find existsLength := by
    by_contra! h
    exact free _ _ pos h (walk.mono wv)
  have prior : QFree D W (Nat.find existsLength-1) := by
    intro z k kl kh road
    have := Nat.find_min' existsLength ⟨z,kl,road⟩
    omega
  have step : Walk D W a a ((Nat.find existsLength-1)+1) := by
    rwa [Nat.sub_add_cancel (by omega)]
  obtain ⟨C,cw,cardC,internal⟩ := boundary_closed_walk_support prior step
  refine ⟨C,cw,by omega,fun v vm=>?_⟩
  have hit := ShellCycleSupply.rooted_on_small_set prior (by omega) cw cardC.le internal vm
  exact ⟨cw.trans wv,vm,hit.one,hit.reaches⟩

/-- Every row of a rooted cycle has an incoming arc within its carrier. -/
theorem reverse_positive {D V C} (large : 1<C.card) (rooted : ∀v∈C,Rooted D V v C) :
    ∀v∈C,1≤(outN (fun a b=>D b a) C v).card := by
  intro v vm
  obtain ⟨a,am⟩ := card_pos.mp (show 0<(C.erase v).card by rw [card_erase_of_mem vm]; omega)
  have av := mem_of_mem_erase am
  obtain ⟨k,w⟩ := (rooted a av).reaches v vm
  cases k with
  | zero => cases w; exact ((mem_erase.mp am).1 rfl).elim
  | succ k =>
    obtain ⟨p,wp,_,arc⟩ := w.unsnoc
    have pm := wp.end_mem_or.elim (fun e=>e.symm ▸ av) id
    exact card_pos.mpr ⟨p,mem_outN.mpr ⟨pm,arc⟩⟩

/-- When a cycle row returns to x, x misses the final q−1 predecessors
of that row, even when the marked cycle is longer than q+1. -/
theorem crossed_omissions {D V Y C q v x} (free : QFree D V q) (hq : 2≤q)
    (yv : Y⊆V) (cy : C⊆Y) (cc : q<C.card) (rc : ∀v∈C,Rooted D V v C)
    (vm : v∈C) (xv : x∈V) (arc : D v x=true) :
    q-1≤(Y\outN D V x).card := by
  let B := ball (fun a b=>D b a) C v (q-2)
  have cv := cy.trans yv
  have size := ball_one_growth (free.reverse.mono_set cv) (reverse_positive (by omega) rc) vm (q-2) (by omega)
  have sub : B⊆Y\outN D V x := by
    intro y ym
    refine mem_sdiff.mpr ⟨cy (ball_subset ym),fun e=>?_⟩
    obtain ⟨_,k,lim,path⟩ := mem_ball.mp ym
    exact free v _ (by omega) (by omega) (.step xv arc (.step (outN_subset e) (mem_outN.mp e).2 ((path.reverse_of_mem vm).mono cv)))
  have := card_le_card sub
  change q-2+1≤B.card at size
  omega

/-- In the equal-width second layer, when the first layer is acyclic, a
physical second-layer cycle cannot point back if depth and quota consume
more than the first-layer row can reserve for omissions. -/
theorem no_back {D V q r u C} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (dag : QFree D (outN D V u) (outN D V u).card)
    (width : (N2 D V u).card=r) (room : r<2*(q-1)) (cy : C⊆N2 D V u)
    (cc : q<C.card) (rc : ∀v∈C,Rooted D V v C) :
    ∀v∈C,∀x∈outN D V u,D v x≠true := by
  intro v vm x xm edge
  let X := outN D V u
  let Y := N2 D V u
  have head t (tm : t∈X) z (zm : z∈outN D V t) : z∈X∪Y :=
    headX (free.mono_bound hq) uv tm (outN_subset zm) (mem_outN.mp zm).2
  obtain ⟨p⟩ := exists_shortest_sink_path dag le_rfl xm
  have sm := p.mem p.len le_rfl
  have sub : outN D V (p.vertex p.len)⊆Y := fun z zm=>(mem_union.mp (head _ sm _ zm)).resolve_left
    (fun zx=>p.sink z zx (mem_outN.mp zm).2)
  have eq := eq_of_subset_of_card_le sub (by rw [reg _ (outN_subset sm)]; exact width.le)
  have sv := (mem_outN.mp (eq.symm ▸ (show v∈Y from cy vm))).2
  have way : Walk D X x (p.vertex p.len) p.len := by
    simpa only [p.start,Nat.sub_zero] using p.walk (Nat.zero_le _) le_rfl
  have late : q-1≤p.len := by
    by_contra! h
    exact free x _ (by omega) (by omega) (((way.mono outN_subset).snoc (N2_subV (cy vm)) sv).snoc (outN_subset xm) edge)
  have inside := SinkTransit.internal_depth dag le_rfl p
  have lost := SinkDepthCover.omitted_heads (reg x (outN_subset xm)).ge (head x xm) (le_refl _)
  have more := crossed_omissions free (by omega) (fun _ m=>N2_subV m) cy cc rc vm (outN_subset xm) edge
  change p.len+(outN D X x).card≤X.card at inside
  change (Y\outN D V x).card+r≤Y.card+(outN D X x).card at lost
  change q-1≤(Y\outN D V x).card at more
  change Y.card=r at width
  have xcard : X.card=r := reg u uv
  omega

/-- This is the cycle selection for *every* low origin. It also bounds
the omission exponent that controls sharing when the cycles overlap. -/
theorem origin {D V q r u} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (width : (N2 D V u).card≤r) (narrow : (N2 D V u).card=r → (N3 D V u).card<r)
    (cut : r<2*(q-1)) (wide : r-(q-2)≤q-1) (bill : (r-(q-2))*((r-(q-2))-1)<2*r) :
    ∃C,(C⊆outN D V u ∨ C⊆N2 D V u) ∧ q<C.card ∧
      (∀v∈C,Rooted D V v C) ∧ omissions D V C r≤r-q := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have cx : X.card=r := reg u uv
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _=>N2_subV
  have menu v (vm : v∈X) z (zm : z∈outN D V v) := headX (free.mono_bound hq) uv vm (outN_subset zm) (mem_outN.mp zm).2
  by_cases dag : QFree D X X.card
  · have pos : 0<r := by omega
    obtain ⟨s,sm,ss⟩ := exists_sink dag (card_pos.mp (by omega)) le_rfl
    have sy : outN D V s⊆Y := fun z zm=>(mem_union.mp (menu s sm z zm)).resolve_left (fun zx=>ss z zx (mem_outN.mp zm).2)
    have equal : Y.card=r := by have := card_le_card sy; rw [reg s (xv sm)] at this; exact le_antisymm width this
    have limit := narrow equal
    have cyclic : ¬QFree D Y Y.card := by
      intro d
      have b := dag_omission free hq reg uv equal limit dag d wide
      have one : 1≤r-(N3 D V u).card := by omega
      have low := Nat.mul_le_mul_left r one
      simp only [Nat.mul_one] at low
      omega
    obtain ⟨C,cy,cc,rc⟩ := actual_cycle free (by omega) yv cyclic
    have reject := no_back free hq reg uv dag equal cut cy cc rc
    have sub : exterior D V C⊆(Y\C)∪Z := by
      intro v vm
      obtain ⟨heads,off⟩ := mem_sdiff.mp vm
      obtain ⟨a,am,edge⟩ := mem_biUnion.mp heads
      have arc := (mem_outN.mp edge).2
      rcases headY (free.mono_bound hq) uv (cy am) (outN_subset edge) arc with early|late
      · exact mem_union_left _ (mem_sdiff.mpr ⟨(mem_union.mp early).resolve_left (fun vx=>reject a am v vx arc),off⟩)
      · exact mem_union_right _ late
    have count := (card_le_card sub).trans (card_union_le _ _)
    rw [card_sdiff_of_subset cy] at count
    change Z.card<r at limit
    refine ⟨C,Or.inr cy,cc,rc,?_⟩
    unfold omissions
    omega
  · obtain ⟨C,cs,cc,rc⟩ := actual_cycle free (by omega) xv dag
    have sub : exterior D V C⊆(X\C)∪Y := by
      intro v vm
      obtain ⟨heads,off⟩ := mem_sdiff.mp vm
      obtain ⟨a,am,edge⟩ := mem_biUnion.mp heads
      rcases mem_union.mp (menu a (cs am) v edge) with vx|vy
      · exact mem_union_left _ (mem_sdiff.mpr ⟨vx,off⟩)
      · exact mem_union_right _ vy
    have count := (card_le_card sub).trans (card_union_le _ _)
    rw [card_sdiff_of_subset cs,cx] at count
    change Y.card≤r at width
    refine ⟨C,Or.inl cs,cc,rc,?_⟩
    unfold omissions
    have := card_le_card cs
    omega

/-- Build the two shell hypotheses from the actual low three-ball. -/
theorem low_origin {D V q r u} (free : QFree D V q) (hq : 6≤q) (reg : OutEq r D V)
    (uv : u∈V) (room : r+2≤2*q) (late : 2*r+3≤3*q+1) (ceiling : 3*r≤4*q+1)
    (pressure : (2*r+1)*(2*r+2)<r*(2*(r+4))+(r+1)*14)
    (cut : r<2*(q-1)) (wide : r-(q-2)≤q-1) (bill : (r-(q-2))*((r-(q-2))-1)<2*r)
    (score : (ball D V u 3).card≤3*r) :
    ∃C,(C⊆outN D V u ∨ C⊆N2 D V u) ∧ q<C.card ∧
      (∀v∈C,Rooted D V v C) ∧ omissions D V C r≤r-q := by
  have small := low_third_second free hq reg uv room late ceiling pressure score
  have a := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg u uv] at a
  have b := @card_B2 D V u
  have c := @card_B3 D V u
  exact origin free (by omega) reg uv (by omega) (by intro eq; omega) cut wide bill
/-- Each low second-shell class receives one actual representative of
minimum score. The candidate cycle stays anchored to that representative.
The family deduplicates literal cycle supports before counting turns. -/
structure Selection (D : CH.Digraph) (V : Finset ℕ) (q r k b : ℕ) where
  rep : Finset ℕ→ℕ
  pay : Finset ℕ→Finset ℕ
  family : Finset (Finset ℕ)
  represents : ∀Y∈(shellOrigins D V k b).image (N2 D V),rep Y∈shellFiber D V k b Y
  least : ∀Y∈(shellOrigins D V k b).image (N2 D V),∀v∈shellFiber D V k b Y,
    (ball D V (rep Y) k).card≤(ball D V v k).card
  assigned : ∀Y∈(shellOrigins D V k b).image (N2 D V),pay Y∈family
  located : ∀Y∈(shellOrigins D V k b).image (N2 D V),pay Y⊆outN D V (rep Y) ∨ pay Y⊆Y
  rooted : ∀C∈family,∀v∈C,Rooted D V v C
  sub : ∀C∈family,C⊆V
  length : ∀C∈family,q<C.card
  loss : ∀C∈family,omissions D V C r≤r-q

theorem select_cycles {D V q r k b} (supply : ∀u∈shellOrigins D V k b,
    ∃C,(C⊆outN D V u ∨ C⊆N2 D V u) ∧ q<C.card ∧
      (∀v∈C,Rooted D V v C) ∧ omissions D V C r≤r-q) :
    Nonempty (Selection D V q r k b) := by
  classical
  let keys := (shellOrigins D V k b).image (N2 D V)
  have least Y (ym : Y∈keys) : ∃u∈shellFiber D V k b Y,∀v∈shellFiber D V k b Y,
      (ball D V u k).card≤(ball D V v k).card := by
    obtain ⟨a,am,eq⟩ := mem_image.mp ym
    exact exists_min_image _ _ ⟨a,mem_filter.mpr ⟨am,eq⟩⟩
  let rep Y := if h:Y∈keys then (least Y h).choose else 0
  have chosen Y (ym : Y∈keys) : rep Y∈shellFiber D V k b Y ∧ ∀v∈shellFiber D V k b Y,
        (ball D V (rep Y) k).card≤(ball D V v k).card := by simpa [rep,ym] using (least Y ym).choose_spec
  have supplies Y (ym : Y∈keys) := supply (rep Y) (mem_filter.mp (chosen Y ym).1).1
  let pay Y := if h:Y∈keys then (supplies Y h).choose else ∅
  have props Y (ym : Y∈keys) :
      (pay Y⊆outN D V (rep Y) ∨ pay Y⊆Y) ∧ q<(pay Y).card ∧
        (∀v∈pay Y,Rooted D V v (pay Y)) ∧ omissions D V (pay Y) r≤r-q := by
    have eq : N2 D V (rep Y)=Y := (mem_filter.mp (chosen Y ym).1).2
    simpa [pay,ym,eq] using (supplies Y ym).choose_spec
  refine ⟨⟨rep,pay,keys.image pay,fun Y ym=>(chosen Y ym).1,fun Y ym=>(chosen Y ym).2,
    fun Y ym=>mem_image_of_mem _ ym,fun Y ym=>(props Y ym).1,?_,?_,?_,?_⟩⟩
  · rintro C cm
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    exact (props Y ym).2.2.1
  · rintro C cm a am
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    exact ((props Y ym).2.2.1 a am).sub am
  · intro C cm
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    exact (props Y ym).2.1
  · intro C cm
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp cm
    exact (props Y ym).2.2.2

theorem native_selection {D V q r} (free : QFree D V q) (hq : 6≤q) (reg : OutEq r D V)
    (room : r+2≤2*q) (late : 2*r+3≤3*q+1) (ceiling : 3*r≤4*q+1)
    (pressure : (2*r+1)*(2*r+2)<r*(2*(r+4))+(r+1)*14)
    (cut : r<2*(q-1)) (wide : r-(q-2)≤q-1) (bill : (r-(q-2))*((r-(q-2))-1)<2*r) :
    Nonempty (Selection D V q r 3 (3*r)) :=
  select_cycles (fun u um=>low_origin (u:=u) free hq reg (mem_filter.mp um).1 room late ceiling pressure cut wide bill (mem_filter.mp um).2)

/-- Compatible numeric regime for obtaining a physical supplier for every
low origin. The three-ball threshold is the one used by low_third_second. -/
def Room (q r : ℕ) : Prop :=
  6≤q ∧ r+2≤2*q ∧ 2*r+3≤3*q+1 ∧ 3*r≤4*q+1 ∧
  (2*r+1)*(2*r+2)<r*(2*(r+4))+(r+1)*14 ∧ r<2*(q-1) ∧ r-(q-2)≤q-1 ∧
  (r-(q-2))*((r-(q-2))-1)<2*r

instance {q r} : Decidable (Room q r) := by unfold Room; infer_instance

/-- Every label of a shell class may be kept as a witness. Its representative
and its cycle are both on the exact thinning supplied by the caller. -/
structure OnFamily (p : CHRuleCatalog.Input) : Prop where
  on_graph : ∀q≤CHRuleCatalog.cutoff p,Room q p.s →
    ∀F,(∀a b,F a b=true → p.D a b=true) → OutEq p.s F (range p.n) →
      Nonempty (Selection F (range p.n) q p.s 3 (3*p.s))

theorem on_bad {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) : OnFamily p := by
  constructor
  rintro q cut ⟨hq,a,b,c,d,e,f,g⟩ G sub reg
  exact native_selection (qfree_sub sub ((qfree_of_noShort bad.loopless bad.missing).mono_bound cut)) hq reg a b c d e f g

/-- A return from b into an acyclic first layer forces the same row x
to miss a reverse ball and to reserve a long path to its own sink. -/
theorem blocked_after_cycle {D V q r u C d v b x} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (uv : u∈V) (dag : QFree D (outN D V u) (outN D V u).card)
    (width : (N2 D V u).card=r) (cy : C⊆N2 D V u) (cc : q<C.card)
    (rc : ∀v∈C,Rooted D V v C) (vm : v∈C) (bm : b∈N2 D V u)
    (road : Walk D V v b d) (xm : x∈outN D V u)
    (time : d+2≤q) (room : r+d<2*(q-1)) : D b x≠true := by
  intro bx
  let X := outN D V u
  let Y := N2 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have cv := cy.trans yv
  have menu t (tm : t∈X) z (zm : z∈outN D V t) := headX (free.mono_bound hq) uv tm (outN_subset zm) (mem_outN.mp zm).2
  obtain ⟨p⟩ := exists_shortest_sink_path dag le_rfl xm
  have sm := p.mem p.len le_rfl
  have sy : outN D V (p.vertex p.len)⊆Y := fun z zm=>(mem_union.mp (menu _ sm _ zm)).resolve_left
    (fun zx=>p.sink z zx (mem_outN.mp zm).2)
  have row := eq_of_subset_of_card_le sy (by rw [reg _ (xv sm)]; exact width.le)
  have sb := (mem_outN.mp (row.symm ▸ (show b∈Y from bm))).2
  have toSink : Walk D X x (p.vertex p.len) p.len := by
    simpa only [p.start,Nat.sub_zero] using p.walk (Nat.zero_le _) le_rfl
  have late : q-1≤p.len := by
    by_contra! h
    exact free x _ (by omega) (by omega) (((toSink.mono xv).snoc (yv bm) sb).snoc (xv xm) bx)
  let B := ball (fun a b=>D b a) C v (q-d-2)
  have size := ball_one_growth (free.reverse.mono_set cv) (reverse_positive (by omega) rc) vm (q-d-2) (by omega)
  have sub : B⊆Y\outN D V x := by
    intro a am
    refine mem_sdiff.mpr ⟨cy (ball_subset am),fun hit=>?_⟩
    obtain ⟨_,k,lim,back⟩ := mem_ball.mp am
    exact free v _ (by omega) (by omega) ((((road.snoc (xv xm) bx).snoc (outN_subset hit) (mem_outN.mp hit).2).append ((back.reverse_of_mem vm).mono cv)))
  have lower := card_le_card sub
  have upper := SinkDepthCover.omitted_heads (reg x (xv xm)).ge (menu x xm) (le_refl _)
  have slots := SinkTransit.internal_depth dag le_rfl p
  change q-d-2+1≤B.card at size
  change p.len+(outN D X x).card≤X.card at slots
  change (Y\outN D V x).card+r≤Y.card+(outN D X x).card at upper
  have order : X.card=r := reg u uv
  change Y.card=r at width
  omega

/-- Every returning exception rules out a ball of possible parents on
the same cycle. This bound allows any cycle length and any return length. -/
theorem exception_parents {D V q C a c l} (free : QFree D V q) (cv : C⊆V)
    (positive : ∀v∈C,1≤(outN D C v).card) (av : a∈V) (cm : c∈C)
    (path : Walk D V a c l) (time : l+1≤q) :
    (inN D C a).card+(q-l)≤C.card := by
  let B := ball D C c (q-l-1)
  have dis : Disjoint (inN D C a) B := by
    apply disjoint_left.mpr
    intro v hit vm
    obtain ⟨_,k,lim,back⟩ := mem_ball.mp vm
    exact free a _ (by omega) (by omega) ((path.append (back.mono cv)).snoc av (mem_inN.mp hit).2)
  have cap := card_le_card (union_subset (show inN D C a⊆C from fun _ h=>(mem_inN.mp h).1) (show B⊆C from ball_subset))
  rw [card_union_of_disjoint dis] at cap
  have grow := ball_one_growth (free.mono_set cv) positive cm (q-l-1) (by omega)
  change q-l-1+1≤B.card at grow
  omega

/-- After a cycle sends an arc to an exceptional second-shell label,
follow a path inside the actual exceptions to a sink. That sink must send
a head back to the same cycle: neither a first-layer head nor the next
shell alone can pay its row. -/
theorem exception_returns {D V q r u C a b} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (dag : QFree D (outN D V u) (outN D V u).card)
    (width : (N2 D V u).card=r) (next : (N3 D V u).card<r) (cy : C⊆N2 D V u)
    (cc : q<C.card) (rc : ∀v∈C,Rooted D V v C)
    (time : (N2 D V u\C).card+2≤q) (fit : r+(N2 D V u\C).card<2*(q-1))
    (ac : a∈C) (bm : b∈N2 D V u\C) (arc : D a b=true) :
    ∃c∈C,∃l≤(N2 D V u\C).card,Walk D V b c l := by
  classical
  let E := N2 D V u\C
  have ev : E⊆V := fun _ m=>N2_subV (mem_sdiff.mp m).1
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set ev) (by dsimp [E]; omega) bm
  have pE := p.mem p.len le_rfl
  have pY := (mem_sdiff.mp pE).1
  have len := p.bounded
  change E.card+2≤q at time
  change r+E.card<2*(q-1) at fit
  have walk : Walk D E b (p.vertex p.len) p.len := by
    simpa only [p.start,Nat.sub_zero] using p.walk (Nat.zero_le _) le_rfl
  have fromC := Walk.step (ev bm) arc (walk.mono ev)
  have back x (xm : x∈outN D V u) := blocked_after_cycle free hq reg uv dag width cy cc rc ac pY fromC xm
    (by omega) (by omega)
  have edge : ∃c∈C,D (p.vertex p.len) c=true := by
    by_contra! no
    have sub : outN D V (p.vertex p.len)⊆N3 D V u := by
      intro z zm
      have az := (mem_outN.mp zm).2
      rcases headY (free.mono_bound hq) uv pY (outN_subset zm) az with early|late
      · obtain xx|yy := mem_union.mp early
        · exact (back _ xx az).elim
        · have off := fun (inside : z∈C)=>no z inside az
          exact (p.sink z (mem_sdiff.mpr ⟨yy,off⟩) az).elim
      · exact late
    have bound := card_le_card sub
    rw [reg _ (ev pE)] at bound
    omega
  obtain ⟨c,cm,edge⟩ := edge
  exact ⟨c,cm,p.len+1,by change _≤E.card; omega,(walk.mono ev).snoc (N2_subV (cy cm)) edge⟩

/-- Count physical cycle rows that send heads to every label of the next
shell. Each exceptional target can spoil at most |C|−(q−|E|) rows. -/
theorem complete_rows {D V q r u C} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (dag : QFree D (outN D V u) (outN D V u).card)
    (width : (N2 D V u).card=r) (next : (N3 D V u).card<r) (cy : C⊆N2 D V u)
    (cc : q<C.card) (rc : ∀v∈C,Rooted D V v C)
    (time : (N2 D V u\C).card+2≤q) (fit : r+(N2 D V u\C).card<2*(q-1)) :
    let E := N2 D V u\C
    let G := C.filter (fun v=>N3 D V u⊆outN D V v)
    C.card≤G.card+E.card*(C.card-(q-E.card)) ∧ (E.card*(C.card-(q-E.card))<C.card → (N3 D V u).card+1=r) := by
  classical
  let E := N2 D V u\C
  let G := C.filter (fun v=>N3 D V u⊆outN D V v)
  let B := E.biUnion (inN D C)
  change C.card≤G.card+E.card*(C.card-(q-E.card)) ∧ (E.card*(C.card-(q-E.card))<C.card → (N3 D V u).card+1=r)
  have cv : C⊆V := fun _ m=>N2_subV (cy m)
  have pos v (vm : v∈C) := ((rc v vm).one v vm).ge
  have bounded b (bm : b∈E) : (inN D C b).card≤C.card-(q-E.card) := by
    by_cases has : (inN D C b).Nonempty
    · obtain ⟨v,hit⟩ := has
      obtain ⟨c,cm,k,lim,walk⟩ := exception_returns free hq reg uv dag width next cy cc rc time fit
        (mem_inN.mp hit).1 bm (mem_inN.mp hit).2
      change k≤E.card at lim
      change E.card+2≤q at time
      have cap := exception_parents free cv pos (N2_subV (mem_sdiff.mp bm).1) cm walk (by omega)
      omega
    · rw [not_nonempty_iff_eq_empty.mp has,card_empty]; omega
  have outside v (vm : v∈C) (hit : v∉B) : r≤1+(outN D (N3 D V u) v).card := by
    have menu : outN D V v⊆outN D C v∪outN D (N3 D V u) v := by
      intro z zm
      have arc := (mem_outN.mp zm).2
      rcases headY (free.mono_bound hq) uv (cy vm) (outN_subset zm) arc with early|late
      · obtain xx|yy := mem_union.mp early
        · exact (no_back free hq reg uv dag width (by omega) cy cc rc v vm z xx arc).elim
        · by_cases zc : z∈C
          · exact mem_union_left _ (mem_outN.mpr ⟨zc,arc⟩)
          · exact (hit (mem_biUnion.mpr ⟨z,mem_sdiff.mpr ⟨yy,zc⟩,mem_inN.mpr ⟨vm,arc⟩⟩)).elim
      · exact mem_union_right _ (mem_outN.mpr ⟨late,arc⟩)
    have need := (card_le_card menu).trans (card_union_le _ _)
    rw [reg _ (cv vm),(rc v vm).one v vm] at need
    exact need
  have cover : C⊆G∪B := by
    intro v vm
    by_cases hit : v∈B
    · exact mem_union_right _ hit
    apply mem_union_left
    apply mem_filter.mpr
    refine ⟨vm,?_⟩
    have need := outside v vm hit
    have eq := eq_of_subset_of_card_le (outN_subset : outN D (N3 D V u) v⊆N3 D V u) (by omega)
    exact fun z zm=>outN_mono (fun _ h=>N3_subV h) v (eq.symm ▸ zm)
  have cap := card_biUnion_le_card_mul E (inN D C) _ bounded
  refine ⟨((card_le_card cover).trans (card_union_le _ _)).trans (Nat.add_le_add_left cap _),?_⟩
  intro few
  obtain ⟨v,vm,miss⟩ : ∃v∈C,v∉B := by
    by_contra! no
    have := card_le_card (show C⊆B from fun v vm=>no v vm)
    change B.card≤_ at cap
    omega
  have count := outside v vm miss
  have := card_le_card (outN_subset : outN D (N3 D V u) v⊆N3 D V u)
  omega

/-- The union of the actual forward balls around the labels of a bank. -/
noncomputable def neighborhood (D : CH.Digraph) (V Z : Finset ℕ) (j : ℕ) : Finset ℕ :=
  Z.biUnion (fun z=>ball D V z j)

/-- For a proposed lower bound on the two-step bank, each possible size
of the one-step bank is excluded by either a retained quota or by the
mixed radius-three demand of its full rows. -/
def ScoreRoom (q r z target : ℕ) : Prop :=
  ∀ h∈Icc (z+r-1) (target-1),
    (∃d∈Icc 2 5,h≤q*d ∧ d+target≤r+h+1) ∨
    (2+target≤r+h+1 ∧ h*(h+1)<z*(2*(r+4))+(h-z)*14)

instance {q r z target} : Decidable (ScoreRoom q r z target) := by
  unfold ScoreRoom; infer_instance

/-- Every member of Z retains its whole row in the one-step bank. The
mixed count and the degree descent hence constrain the two-step union
for any physical set Z, regardless of its origin. -/
theorem bank_growth {D V Z q r target} (free : QFree D V q) (hq : 6≤q) (reg : OutEq r D V)
    (zv : Z⊆V) (live : Z.Nonempty) (small : Z.card≤2*q) (room : r+2≤2*q)
    (guards : ScoreRoom q r Z.card target) : target≤(neighborhood D V Z 2).card := by
  classical
  let H := neighborhood D V Z 1
  let T := neighborhood D V Z 2
  have zh : Z⊆H := fun z zm=>mem_biUnion.mpr ⟨z,zm,self_mem_ball (zv zm)⟩
  have ht : H⊆T := by
    intro x xm; obtain ⟨z,zm,inBall⟩ := mem_biUnion.mp xm
    exact mem_biUnion.mpr ⟨z,zm,ball_mono_radius (by decide : 1≤2) inBall⟩
  have hv : H⊆V := by intro x xm; obtain ⟨_,_,inBall⟩ := mem_biUnion.mp xm; exact ball_subset inBall
  have inH z (zm : z∈Z) : outN D V z⊆outN D H z := by
    intro x xm
    exact mem_outN.mpr ⟨mem_biUnion.mpr ⟨z,zm,ball_of_adj (outN_subset xm) (mem_outN.mp xm).2⟩,(mem_outN.mp xm).2⟩
  have inT x (xm : x∈H) : outN D V x⊆T := by
    obtain ⟨z,zm,inBall⟩ := mem_biUnion.mp xm
    intro a am
    exact mem_biUnion.mpr ⟨z,zm,ball_step inBall (outN_subset am) (mem_outN.mp am).2⟩
  have full z (zm : z∈Z) : r≤(outN D H z).card := (reg z (zv zm)).symm ▸ card_le_card (inH z zm)
  have loss {S O : Finset ℕ} (so : S⊆O) {x} (within : outN D V x⊆O) (xm : x∈V) :
      r+S.card≤(outN D S x).card+O.card := by
    have sub : outN D V x⊆outN D S x∪(O\S) := by
      intro a am
      by_cases hit : a∈S
      · exact mem_union_left _ (mem_outN.mpr ⟨hit,(mem_outN.mp am).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨within am,hit⟩)
    have bound := (card_le_card sub).trans (card_union_le _ _)
    rw [reg x xm,card_sdiff_of_subset so] at bound
    have := card_le_card so
    omega
  have floor : Z.card+r-1≤H.card := by
    by_contra! low
    have paid z (zm : z∈Z) : 2≤(outN D Z z).card := by
      have := loss zh (fun _ a=>outN_subset (inH z zm a)) (zv zm)
      omega
    have := corB (by omega : 1≤q) (free.mono_set zv) paid live
    omega
  by_contra! fail
  change T.card<target at fail
  have size := card_le_card ht
  have cell := guards H.card (mem_Icc.mpr ⟨floor,by omega⟩)
  have kept x (xm : x∈H) := loss ht (inT x xm) (hv xm)
  rcases cell with ⟨d,dm,cap,quota⟩|⟨quota,cap⟩
  · obtain ⟨lo,hi⟩ := mem_Icc.mp dm
    have lower := BRq6.lower_order (by omega : 5≤q) lo (by omega : d<6) (free.mono_set hv)
      (fun x xm=>by have := kept x xm; omega) (live.mono zh)
    omega
  · have ranks x (xm : x∈H) : 2≤(outN D H x).card := by have := kept x xm; omega
    have bound := RetainedMixedCapacity.mixed_capacity (i:=3) (j:=3) (base:=14) (high:=2*(r+4))
      (free.mono_set hv) (by omega) zh
      (fun x xm=>by have := ball_growth q (by omega) D H (free.mono_set hv) ranks x xm 3 (by omega); omega)
      (fun x xm=>by have := FullRowEscape.high_third (free.mono_set hv) (by omega) ranks (zh xm) (full x xm) room; omega)
    omega

/-- A full cycle row sees the bank two steps farther than its first
head. When the other cycle rows can find a full row soon enough,
none of these bank labels is on the cycle, so both counts are additive. -/
theorem score_from_bank {D V C Z q m target v} (free : QFree D V q) (cv : C⊆V) (zv : Z⊆V)
    (rc : ∀x∈C,1≤(outN D C x).card) (hq : 4≤q) (time : m+3≤q) (vm : v∈C)
    (full : Z⊆outN D V v) (near : C.card≤(C.filter (fun a=>Z⊆outN D V a)).card+m)
    (bound : target≤(neighborhood D V Z 2).card) : 4+target≤(ball D V v 3).card := by
  classical
  let G := C.filter (fun a=>Z⊆outN D V a)
  have sub : G⊆C := filter_subset _ _
  have reach a (am : a∈C) : ∃g∈G,g∈ball D C a m := by
    by_contra! no
    have incl : ball D C a m⊆C\G := fun g gm=>mem_sdiff.mpr ⟨ball_subset gm,fun gg=>no g gg gm⟩
    have size := card_le_card incl
    rw [card_sdiff_of_subset sub] at size
    have more := ball_one_growth (free.mono_set cv) rc am m (by omega)
    have := card_le_card sub
    change C.card≤G.card+m at near
    omega
  have dis : Disjoint C (neighborhood D V Z 2) := by
    refine disjoint_left.mpr (fun a am reached=>?_ )
    obtain ⟨z,zm,inBall⟩ := mem_biUnion.mp reached
    obtain ⟨_,k,lim,toA⟩ := mem_ball.mp inBall
    obtain ⟨g,gm,atG⟩ := reach a am
    obtain ⟨_,j,fit,toG⟩ := mem_ball.mp atG
    have gz := (mem_outN.mp ((mem_filter.mp gm).2 zm)).2
    exact free z _ (by omega) (by omega) ((toA.append (toG.mono cv)).snoc (zv zm) gz)
  have inc : ball D C v 3∪neighborhood D V Z 2⊆ball D V v 3 := by
    apply union_subset (ShellCycleSupply.lift_ball cv)
    intro a am
    obtain ⟨z,zm,hit⟩ := mem_biUnion.mp am
    obtain ⟨av,k,lim,toA⟩ := mem_ball.mp hit
    exact mem_ball.mpr ⟨av,k+1,by omega,.step (zv zm) (mem_outN.mp (full zm)).2 toA⟩
  have count := card_le_card inc
  rw [card_union_of_disjoint (dis.mono_left ball_subset)] at count
  have more := ball_one_growth (free.mono_set cv) rc vm 3 (by omega)
  omega

/-- Join the exceptional-target count to the two-step bank-growth
bound. The rows counted in the conclusion are the same rows which see
the entire bank, on the supplied physical cycle. -/
theorem scored_second_cycle {D V q r u C target} (free : QFree D V q) (hq : 6≤q) (reg : OutEq r D V)
    (uv : u∈V) (dag : QFree D (outN D V u) (outN D V u).card)
    (width : (N2 D V u).card=r) (next : (N3 D V u).card<r) (cy : C⊆N2 D V u)
    (cc : q<C.card) (rc : ∀v∈C,Rooted D V v C) (room : r+2≤2*q)
    (time : (N2 D V u\C).card+2≤q) (fit : r+(N2 D V u\C).card<2*(q-1))
    (near : (N2 D V u\C).card*(C.card-(q-(N2 D V u\C).card))+3≤q)
    (guard : ScoreRoom q r (r-1) target) :
    let E := N2 D V u\C
    let G := C.filter (fun a=>N3 D V u⊆outN D V a)
    (N3 D V u).card+1=r ∧ C.card≤G.card+E.card*(C.card-(q-E.card)) ∧
      ∀v∈G,4+target≤(ball D V v 3).card := by
  classical
  let E := N2 D V u\C
  let Z := N3 D V u
  let G := C.filter (fun a=>Z⊆outN D V a)
  let m := E.card*(C.card-(q-E.card))
  change m+3≤q at near
  have rows := complete_rows free (by omega) reg uv dag width next cy cc rc time fit
  change C.card≤G.card+m ∧ (m<C.card → Z.card+1=r) at rows
  have zsize := rows.2 (by omega)
  have lower := card_le_card cy
  have live := card_pos.mp (show 0<Z.card by omega)
  have zv : Z⊆V := fun _ h=>N3_subV h
  have stock := bank_growth free hq reg zv live (by omega) room
    (by simpa [show Z.card=r-1 by omega] using guard)
  refine ⟨zsize,rows.1,?_⟩
  intro v vm
  have vg := mem_filter.mp vm
  exact score_from_bank free (fun _ h=>N2_subV (cy h)) zv (fun a am=>((rc a am).one a am).ge)
    (by omega) near vg.1 vg.2 rows.1 stock

/-- Each exceptional label costs at most r−q complete rows when the
second layer has r labels. The cycle and its full, high rows are
generated from a low three-ball and an acyclic first layer. -/
theorem marked_stock {D V q r u C target} (free : QFree D V q) (reg : OutEq r D V) (uv : u∈V)
    (hr : 0<r) (regime : Room q r) (low : (ball D V u 3).card≤3*r)
    (dag : QFree D (outN D V u) (outN D V u).card)
    (loc : C⊆outN D V u ∨ C⊆N2 D V u) (cc : q<C.card) (rc : ∀v∈C,Rooted D V v C)
    (exceptionFit : r+(r-(q+1))<2*(q-1)) (distance : (r-(q+1))*(r-q)+3≤q)
    (guard : ScoreRoom q r (r-1) target) :
    C⊆N2 D V u ∧
      (N3 D V u).card+1=r ∧
      let G := C.filter (fun a=>N3 D V u⊆outN D V a)
      C.card≤G.card+(r-C.card)*(r-q) ∧ ∀v∈G,4+target≤(ball D V v 3).card := by
  obtain ⟨hq,a,b,c,d,e,f,g⟩ := regime
  have cap := low_third_second free hq reg uv a b c d low
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg u uv] at one
  have two := @card_B2 D V u
  have three := @card_B3 D V u
  have cx := reg u uv
  obtain ⟨s,sm,ss⟩ := exists_sink dag (card_pos.mp (by omega)) le_rfl
  have sy : outN D V s⊆N2 D V u := fun z hm=>(mem_union.mp (headX (free.mono_bound (by omega : 4≤q))
    uv sm (outN_subset hm) (mem_outN.mp hm).2)).resolve_left (fun xm=>ss z xm (mem_outN.mp hm).2)
  have lower := card_le_card sy
  rw [reg s (outN_subset sm)] at lower
  have width : (N2 D V u).card=r := by omega
  have next : (N3 D V u).card<r := by omega
  have cy : C⊆N2 D V u := by
    rcases loc with inside|outside
    · obtain ⟨y,ym,stop⟩ := exists_sink (dag.mono_set inside) (card_pos.mp (by omega)) (card_le_card inside)
      obtain ⟨v,hm⟩ := card_pos.mp (show 0<(outN D C y).card by rw [(rc y ym).one y ym]; decide)
      exact (stop _ (outN_subset hm) (mem_outN.mp hm).2).elim
    · exact outside
  have sizes := card_le_card cy
  have extras := card_sdiff_of_subset cy
  have cost : C.card-(q-(N2 D V u\C).card)=r-q := by omega
  have near := Nat.mul_le_mul_right (r-q) (show (N2 D V u\C).card≤r-(q+1) by omega)
  obtain ⟨sz,bound,paid⟩ := scored_second_cycle free hq reg uv dag width next cy cc rc a
    (by omega) (by omega) (by rw [cost]; omega) guard
  rw [cost,extras,width] at bound
  exact ⟨cy,sz,bound,paid⟩

/-- Price the cycle already selected for this literal second-shell class.
There is no reselection of the cycle when turning its rows into surplus. -/
theorem selected_stock {D V q r target Y} (free : QFree D V q) (reg : OutEq r D V) (hr : 0<r)
    (sel : Selection D V q r 3 (3*r)) (ym : Y∈(shellOrigins D V 3 (3*r)).image (N2 D V))
    (regime : Room q r) (dag : QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card)
    (exceptionFit : r+(r-(q+1))<2*(q-1)) (distance : (r-(q+1))*(r-q)+3≤q)
    (guard : ScoreRoom q r (r-1) target) :
    let C := sel.pay Y
    let Z := N3 D V (sel.rep Y)
    let G := C.filter (fun a=>Z⊆outN D V a)
    C⊆Y ∧ Z.card+1=r ∧ C.card≤G.card+(r-C.card)*(r-q) ∧ ∀v∈G,4+target≤(ball D V v 3).card := by
  have rep := mem_filter.mp (sel.represents Y ym)
  have low := mem_filter.mp rep.1
  have here := (sel.located Y ym).imp_right (fun h=>h.trans rep.2.symm.subset)
  have support := sel.assigned Y ym
  have gain := marked_stock free reg low.1 hr regime low.2 dag here (sel.length _ support)
    (sel.rooted _ support) exceptionFit distance guard
  exact ⟨gain.1.trans rep.2.subset,gain.2⟩

/-- Count actual ordered holes inside each group of origins. A physical
pair can be used for at most one cycle. -/
noncomputable def group (D : CH.Digraph) (V : Finset ℕ) (k b : ℕ) (pay : Finset ℕ → Finset ℕ) (C : Finset ℕ) :=
  (shellOrigins D V k b).filter (fun v=>pay (N2 D V v)=C)

noncomputable def groupHoles (D : CH.Digraph) (V : Finset ℕ) (k b : ℕ) (pay : Finset ℕ → Finset ℕ) (C : Finset ℕ) :=
  (group D V k b pay C).offDiag ∩ DotClonePairCompletion.orderedIncomparable D V k

/-- A closing test on the physical assignment with every admissible within-group
hole already credited. The hole sets and their disjointness are automatic. -/
theorem group_exit {D V q r k b} (free : QFree D V q) (time : k+k≤q) (reg : OutEq r D V)
    (floor : ∀v∈V,b≤(ball D V v k).card+1) (size : V.card≤2*b) (sel : Selection D V q r k b)
    (paid : ∀C∈sel.family,
      (∑v∈group D V k b sel.pay C,(debit b (ball D V v k).card : ℚ)) ≤
        (groupHoles D V k b sel.pay C).card+
        ∑v∈C,share D V sel.family r (fun v=>surplus b (ball D V v k).card) C v)
    (strict : ∃C∈sel.family,
      (∑v∈group D V k b sel.pay C,(debit b (ball D V v k).card : ℚ)) <
        (groupHoles D V k b sel.pay C).card+
        ∑v∈C,share D V sel.family r (fun v=>surplus b (ball D V v k).card) C v) : False := by
  classical
  let origins := shellOrigins D V k b
  let vals := fun v=>(debit b (ball D V v k).card : ℚ)
  let holes := groupHoles D V k b sel.pay
  have assign : ∀v∈origins,sel.pay (N2 D V v)∈sel.family := fun v vm=>sel.assigned _ (mem_image_of_mem _ vm)
  have apart : (sel.family : Set (Finset ℕ)).PairwiseDisjoint holes := by
    intro C _ K _ ne
    apply disjoint_left.mpr
    intro x xc xk
    have a := (mem_filter.mp (mem_offDiag.mp (mem_inter.mp xc).1).1).2
    have b := (mem_filter.mp (mem_offDiag.mp (mem_inter.mp xk).1).1).2
    exact ne (a.symm.trans b)
  have groupSum : (∑ C∈sel.family,∑ v∈group D V k b sel.pay C,vals v)=∑v∈origins,vals v :=
    sum_fiberwise_of_maps_to assign _
  have off : ∑v∈V\origins,vals v=0 := by
    apply sum_eq_zero
    intro v vm
    have gt : b<(ball D V v k).card := by
      by_contra! sm
      exact (mem_sdiff.mp vm).2 (mem_filter.mpr ⟨(mem_sdiff.mp vm).1,sm⟩)
    simp [vals,debit,not_lt_of_ge gt.le,Nat.ne_of_gt gt]
  have all := sum_sdiff (filter_subset _ _ : origins⊆V) (f:=vals)
  change (∑v∈V\origins,vals v)+(∑v∈origins,vals v)=_ at all
  rw [off,zero_add] at all
  have money := sum_lt_sum paid strict
  change (∑ C∈sel.family,∑ v∈group D V k b sel.pay C,vals v)<_ at money
  rw [groupSum,all,sum_add_distrib] at money
  have real : sel.family.biUnion holes⊆DotClonePairCompletion.orderedIncomparable D V k := by
    intro e em
    obtain ⟨_,_,inside⟩ := mem_biUnion.mp em
    exact (mem_inter.mp inside).2
  have unique : ((sel.family.biUnion holes).card : ℚ)=∑ C∈sel.family,((holes C).card : ℚ) := by
    exact_mod_cast card_biUnion apart
  apply ledger_contradiction free time floor size sel.rooted sel.sub reg real
  rw [unique]
  exact money

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] on_bad
attribute [aesop safe forward (immediate := [free,reg,hr,sel,ym,regime,dag,exceptionFit,distance,guard])
  (rule_sets := [CHGraphFamilies])] selected_stock
attribute [aesop safe forward (immediate := [free,time,reg,floor,size,sel,paid,strict])
  (rule_sets := [CHGraphFamilies])] group_exit

#print axioms on_bad
#print axioms selected_stock
#print axioms marked_stock
#print axioms bank_growth
#print axioms score_from_bank
#print axioms scored_second_cycle
#print axioms complete_rows
#print axioms exception_returns
#print axioms group_exit
#print axioms native_selection
#print axioms origin
#print axioms low_origin
#print axioms actual_cycle
#print axioms crossed_omissions
#print axioms no_back
end LeanCH.BR.LowShellCycleSelection
