import checkpoints.shen_extension.LastArcSeparatorSink
import checkpoints.shen_extension.SharedArcBudget

namespace LeanCH.BR.Closure.LastArcMergePayment
open Finset BRq2 BRq3 BR45 WeightedSD FiniteCutInverse FirstPacketBarrier
open ShortestCycleWeights SharedArcBarrier SharedArcComponentExchange ShenCycleSuccessor
open MarkedCyclePeeling hiding Arc

/-- Cost a native distinguishing row in the current selected graph's flat
allocation. The arc to the charged target is actually present in that graph. -/
structure Priced {q n} (X : Model q n) (G : CH.Digraph) (w : ℕ→ℚ)
    (s t r : ℕ) : Prop where
  oldArc : G s t=true
  misses : X.D s r=false
  cap : WeightedSD.row q X.D X.V w s + (if s=r then w t else 0) ≤ 1 + (q:ℚ)*w t

private theorem row_le_native {q n} (X : Model q n) {G : CH.Digraph}
    (sub : ∀ i j, G i j=true → X.D i j=true) {w : ℕ→ℚ} (pos : ∀ i∈X.V,0≤w i)
    {s} (sv : s∈X.V) : WeightedSD.row q G X.V w s ≤ WeightedSD.row q X.D X.V w s :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (outW_mono_graph (fun i _ j _ => sub i j) pos sv) (Nat.cast_nonneg _))

private theorem missing_cost {q n} (X : Model q n) {G : CH.Digraph}
    (sub : ∀ i j,G i j=true → X.D i j=true) {w : ℕ→ℚ} (pos : ∀i∈X.V,0≤w i)
    {s v} (_sv : s∈X.V) (vv : v∈X.V) (arc : X.D s v=true) (off : G s v=false) :
    WeightedSD.row q G X.V w s + (q:ℚ)*w v ≤ WeightedSD.row q X.D X.V w s := by
  have sum : outW G X.V w s + w v ≤ outW X.D X.V w s := by
    rw [outW_erase (D:=G) vv w s,outW_erase (D:=X.D) vv w s]
    simp only [arc,off,ite_true,Bool.false_eq_true,ite_false,add_zero]
    apply add_le_add _ le_rfl
    apply sum_le_sum
    intro j jv
    by_cases hit : G s j=true
    · simp [hit,sub s j hit]
    · by_cases dh : X.D s j=true <;> simp [hit,dh,pos j (mem_of_mem_erase jv)]
  have mul := mul_le_mul_of_nonneg_left sum (Nat.cast_nonneg q : (0:ℚ) ≤ q)
  unfold WeightedSD.row
  linarith only [mul]

theorem priced_parent {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    {G : CH.Digraph} (sub : ∀ i j,G i j=true → X.D i j=true)
    {w ρ d} (flat : OmittedCycleProgress.Flat q G X.V w ρ d)
    {t r} (tv : t∈X.V) (rv : r∈X.V) (diff : t≠r) :
    ∃ s∈X.V, Priced X G w s t r := by
  classical
  obtain ⟨high,pos,_,norm,_,rows,_⟩ := flat
  have nonneg (i) (iv : i∈X.V) := (pos i iv).le
  have rin := mem_erase.mpr ⟨Ne.symm diff,rv⟩
  have transferred (i) (iv : i∈X.V.erase t) : 0 ≤ transferWeight w t r i := by
    unfold transferWeight
    split_ifs <;> linarith [nonneg i (mem_of_mem_erase iv),nonneg t tv]
  obtain ⟨s,sk,low⟩ := small X.D (X.V.erase t) (card_erase_lt_of_mem tv)
    (X.free.mono_set (erase_subset _ _)) _ transferred ⟨r,rin⟩
  have sv := mem_of_mem_erase sk
  have floor := (rows s sv) ▸ row_le_native X sub nonneg sv
  have exactRow := outW_erase (D:=X.D) tv w s
  rw [mass_transfer tv rv diff,norm,WeightedSD.row,outW_transfer (D:=X.D) rin] at low
  unfold transferWeight at low
  have bonus : (0:ℚ)≤(if s=r then w t else 0) := by split_ifs <;> simp [nonneg t tv]
  have qw := mul_nonneg (Nat.cast_nonneg q : (0:ℚ)≤q) (nonneg t tv)
  have native : X.D s t=true ∧ X.D s r=false ∧
      WeightedSD.row q X.D X.V w s + (if s=r then w t else 0) ≤ 1+(q:ℚ)*w t := by
    unfold WeightedSD.row at floor ⊢
    rw [exactRow] at floor ⊢
    cases a : X.D s t <;> cases b : X.D s r <;>
      simp only [a,b,ite_true,Bool.false_eq_true,ite_false,add_zero,mul_add] at floor low ⊢ <;>
      simp_all only [true_and,Bool.false_eq_true,false_and] <;> linarith
  have old : G s t=true := by
    by_contra! off
    have cost := missing_cost X sub nonneg sv tv native.1 (by simpa using off)
    rw [rows s sv] at cost
    linarith only [native.2.2,high,bonus,cost]
  exact ⟨s,sv,old,native.2.1,native.2.2⟩

/-- At a merged pivot s=r, the other parent's weight pays for every missing
native head of s. In particular it must strictly exceed the common head's weight. -/
theorem merge_price {q n} (X : Model q n) {G : CH.Digraph}
    (sub : ∀i j,G i j=true → X.D i j=true) {w ρ d}
    (flat : OmittedCycleProgress.Flat q G X.V w ρ d)
    {r t v} (rv : r∈X.V) (vv : v∈X.V) (native : X.D r v=true) (missing : G r v=false)
    (priced : Priced X G w r t r) :
    d-1+(q:ℚ)*w v ≤ ((q:ℚ)-1)*w t := by
  obtain ⟨_,pos,_,_,_,rows,_⟩ := flat
  have cost := missing_cost X sub (fun i iv => (pos i iv).le) rv vv native missing
  rw [rows r rv] at cost
  have upper := priced.cap
  simp only [ite_true] at upper
  linarith

/-- At a collision every marked tail is at distance at most q-1. A too-late
mark would consume the one deletion while the collision requires another. -/
theorem no_late_tail {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B) (least : LastArcDistanceConflict.Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D (insert B F) u v=false)
    {f g : Arc} (fm : f∈added X.D F B) (gm : g∈added X.D F B) (diff : f≠g)
    (collision : PuncturedDistance.depth X.D X.V v.val f.1=PuncturedDistance.depth X.D X.V v.val g.1) :
    ∀ h∈added X.D F B, PuncturedDistance.depth X.D X.V v.val h.1 < q := by
  classical
  obtain ⟨S,sub,size,layout⟩ := LastArcDistanceConflict.return_positions X hq small step least bad u v uv off
  let P := added X.D F B
  have few : (P\S).card ≤ 1 := by rw [card_sdiff_of_subset sub]; omega
  have good (h : Arc) (mem : h∈S) : PuncturedDistance.depth X.D X.V v.val h.1<q := by
    have sum := layout.1 h mem
    dsimp only at sum
    omega
  have lost : f∉S ∨ g∉S := by
    by_contra! kept
    exact diff (layout.2.1 kept.1 kept.2 collision)
  intro h hm
  by_contra! late
  have hout : h∈P\S := mem_sdiff.mpr ⟨hm,fun m => (good h m).not_ge late⟩
  have same (z : Arc) (zm : z∈P) (zz : z∉S) : z=h :=
    card_le_one.mp few _ (mem_sdiff.mpr ⟨zm,zz⟩) _ hout
  have pairLate : q≤PuncturedDistance.depth X.D X.V v.val f.1 := by
    rcases lost with lf|lg
    · simpa only [same f fm lf] using late
    · rw [collision,same g gm lg]; exact late
  have lf : f∉S := fun m => (good f m).not_ge pairLate
  have lg : g∉S := fun m => (good g m).not_ge (collision ▸ pairLate)
  exact diff ((same f fm lf).trans (same g gm lg).symm)

/-- At the original gate, an installed arc leaving a native parent of a
colliding head must already belong to the family BEFORE its minimum packet. -/
theorem parent_arc_in_base {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B) (least : LastArcDistanceConflict.Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D (insert B F) u v=false)
    {f g : Arc} (fm : f∈added X.D F B) (gm : g∈added X.D F B) (diff : f≠g)
    (coll : PuncturedDistance.depth X.D X.V v.val f.1=PuncturedDistance.depth X.D X.V v.val g.1)
    {r j : ℕ} (rv : r∈X.V) (edge : X.D r v=true) (old : graph X.D (insert B F) r j=true) :
    graph X.D F r j=true := by
  rcases union_arc.mp old with yes|mark
  · exact yes
  obtain ⟨C,cy,rc,vc⟩ := ShortestCycleWeights.edge_cycle X hq rv v.property edge
  have ne : v.val≠r := by rintro same; exact loopfree X.free (by omega) rv (same ▸ edge)
  obtain ⟨_,cap,fw,back⟩ := MandatoryExcursion.segments (by omega) X.free cy vc rc
  simp only [MandatoryExcursion.span,ite_eq_right ne] at cap fw back
  have early := no_late_tail X hq small step least bad u v uv off fm gm diff coll (r,j) mark
  change PuncturedDistance.depth X.D X.V v.val r < q at early
  exact (X.free v.val _ (by omega) (by omega) ((fw.mono cy.sub).snoc v.property edge)).elim

/-- The pivot arc is already paid in the base. Attaching the alternative
changes neither the pivot row nor the other parent's column. All new bills
are elsewhere; the missing head v is exterior to this cycle as well. -/
theorem original_bills {q n F L r t v} (X : Model q n) (cy : Cycle X.D X.V q L)
    (rl : r∈L) (tl : t∈L) (vl : v∉L) (base : graph X.D F r t=true) :
    (∀ j,graph X.D (insert L F) r j=graph X.D F r j) ∧
    (∀ i,graph X.D (insert L F) i t=graph X.D F i t) ∧
    (∀ i,graph X.D (insert L F) i v=graph X.D F i v) ∧
    ∀ p,RealDual q (graph X.D F) X.V 1 p →
      (RealDual q (graph X.D (insert L F)) X.V 1 p ↔
        ∀ a∈L,∀ b∈L,a≠r → b≠t → b≠v → X.D a b=true → graph X.D F a b=false →
          realCol q (graph X.D F) X.V p b+q*p a≤1) := by
  classical
  have rt := CrossValueOmissions.selected_sub base
  have labels {a b} (al : a∈L) (bl : b∈L) (edge : X.D a b=true) (off : graph X.D F a b=false) :
      a≠r ∧ b≠t ∧ b≠v := by
    constructor
    · rintro rfl
      have eq := card_le_one.mp (cy.heads a al).le _ (mem_outN.mpr ⟨bl,edge⟩) _ (mem_outN.mpr ⟨tl,rt⟩)
      exact Bool.noConfusion (off.symm.trans (eq ▸ base))
    constructor
    · rintro rfl
      have eq := card_le_one.mp (cy.incoming b bl).le _ (mem_inN.mpr ⟨al,edge⟩) _ (mem_inN.mpr ⟨rl,rt⟩)
      exact Bool.noConfusion (off.symm.trans (eq ▸ base))
    · exact fun eq => vl (eq ▸ bl)
  have unchanged {a b} (fixed : a=r ∨ b=t ∨ b=v) :
      graph X.D (insert L F) a b=graph X.D F a b := by
    apply Bool.eq_iff_iff.mpr ⟨?_,fun old => union_arc.mpr (Or.inl old)⟩
    intro ed
    rcases union_arc.mp ed with old|mark
    · exact old
    obtain ⟨al,bl,edge,off⟩ := mem_added.mp mark
    have ⟨x,y,z⟩ := labels al bl edge off
    exact (fixed.elim x (fun alt=>alt.elim y z)).elim
  refine ⟨fun _=>unchanged (Or.inl rfl),fun _=>unchanged (Or.inr (Or.inl rfl)),
    fun _=>unchanged (Or.inr (Or.inr rfl)),?_⟩
  intro p hp
  rw [SharedArcBudget.fits_iff cy hp]
  constructor
  · intro fix a al b bl _ _ _ e off; exact fix a al b bl e off
  · intro fix a al b bl e off
    obtain ⟨x,y,z⟩ := labels al bl e off
    exact fix a al b bl x y z e off

private theorem cycle_depth_injective {q n B v} (X : Model q n) (hq : 2≤q) (cy : Cycle X.D X.V q B)
    (vb : v∈B) : Set.InjOn (PuncturedDistance.depth X.D X.V v) (B : Set ℕ) := by
  have walk {b} (bb : b∈B) : Walk X.D B v b (PuncturedDistance.depth X.D X.V v b) := by
    by_cases eq : v=b
    · subst b
      exact (Nat.eq_zero_of_le_zero (PuncturedDistance.depth_le_walk (Walk.refl (D:=X.D) (W:=X.V) v))) ▸ Walk.refl v
    · simpa only [MandatoryExcursion.span,ite_eq_right eq] using
        (MandatoryExcursion.segments (by omega : 1≤q) X.free cy vb bb).2.2.1
  have unique {k x i j} (xb : x∈B) (wi : Walk X.D B x i k) (wj : Walk X.D B x j k) : i=j := by
    induction k generalizing x i j with
    | zero => cases wi; cases wj; rfl
    | succ k ih =>
      cases wi with
      | @step _ a _ _ ab xa ai =>
        cases wj with
        | @step _ b _ _ bb xx bj =>
          have eq := card_le_one.mp (cy.heads x xb).le _ (mem_outN.mpr ⟨ab,xa⟩) _ (mem_outN.mpr ⟨bb,xx⟩)
          subst b
          exact ih ab ai bj
  intro i ib j jb same
  exact unique vb (walk ib) (same ▸ walk jb)

/-- Two different cycles retaining k positive old arcs share at least k+1
vertices. A sink of their proper intersection cannot tail any retained arc. -/
private theorem retained_vertices {q n F B M S} (X : Model q n) (cb : Cycle X.D X.V q B)
    (cm : Cycle X.D X.V q M) (different : B≠M)
    (live : S.Nonempty) (inB : S⊆added X.D F B) (inM : S⊆added X.D F M) :
    S.card < (B∩M).card := by
  classical
  obtain ⟨e,es⟩ := live
  have interior : (B∩M).Nonempty := ⟨e.1,mem_inter.mpr ⟨(mem_added.mp (inB es)).1,(mem_added.mp (inM es)).1⟩⟩
  have bound : (B∩M).card≤q := by
    have strict : B∩M ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left,fun eq =>
      different (eq_of_subset_of_card_le (by calc B = B∩M := eq.symm
                                                  _ ⊆ M := inter_subset_right) (by rw [cb.size,cm.size]))⟩
    have lt := card_lt_card strict
    rw [cb.size] at lt
    omega
  obtain ⟨z,zm,sink⟩ := exists_sink (X.free.mono_set (inter_subset_left.trans cb.sub)) interior bound
  have labels : S.image Prod.fst ⊆ (B∩M).erase z := by
    intro i im
    obtain ⟨p,ps,rfl⟩ := mem_image.mp im
    obtain ⟨pb,qb,ed,_⟩ := mem_added.mp (inB ps)
    obtain ⟨pm,qm,_,_⟩ := mem_added.mp (inM ps)
    exact mem_erase.mpr ⟨fun eq => sink p.2 (mem_inter.mpr ⟨qb,qm⟩) (eq ▸ ed),mem_inter.mpr ⟨pb,pm⟩⟩
  have sz := card_le_card labels
  rw [card_image_of_injOn (fun f ff g gg eq => matching cb (inB ff) (inB gg) (Or.inl eq))] at sz
  exact sz.trans_lt (card_erase_lt_of_mem zm)

/-- Replaying a missing arc at a packet with q marks can introduce at most
one vertex outside the original cycle. -/
private theorem full_replay {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B) (least : LastArcDistanceConflict.Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) (full : (added X.D F B).card=q)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D (insert B F) u v=false) :
    ∃ M, Cycle X.D X.V q M ∧ u.val∈M ∧ v.val∈M ∧ (B\M).card≤1 ∧ (M\B).card≤1 := by
  classical
  obtain ⟨M,bm,em,alt⟩ := LastArcCompetitor.packet X hq small step least bad u v uv off
  have cm : Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have ne : B≠M := by rintro rfl; exact Bool.noConfusion (off.symm.trans (union_arc.mpr (Or.inr em)))
  have overlap : q ≤ (B∩M).card := by
    rcases alt with ⟨eq,_⟩ | ⟨f,fp,eq⟩
    · have inside : added X.D F B⊆added X.D F M := eq ▸ subset_insert _ _
      have live := card_pos.mp (show 0<(added X.D F B).card by omega)
      have lt := retained_vertices X cb cm ne live Subset.rfl inside
      omega
    · let S := (added X.D F B).erase f
      have cnt : S.card+1=q := (card_erase_add_one fp).trans full
      have inside : S⊆added X.D F M := eq ▸ subset_insert _ _
      have live := card_pos.mp (show 0<S.card by omega)
      have lt := retained_vertices X cb cm ne live (erase_subset _ _) inside
      omega
  have left := card_sdiff_add_card_inter B M
  have right := card_sdiff_add_card_inter M B
  rw [inter_comm M B] at right
  rw [cb.size] at left
  rw [cm.size] at right
  exact ⟨M,cm,(mem_added.mp em).1,(mem_added.mp em).2.1,by omega,by omega⟩

/-- A head outside a maximum-size packet cannot have two missing parents.
The two replays would force the two opposite arcs between those parents. -/
theorem outside_unique_parent {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B) (least : LastArcDistanceConflict.Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) (full : (added X.D F B).card=q)
    (t r v : X.V) (outside : v.val∉B)
    (tv : X.D t v=true) (rt : graph X.D (insert B F) t v=false)
    (rv : X.D r v=true) (rr : graph X.D (insert B F) r v=false) : t=r := by
  classical
  by_contra ne
  have diff : t.val≠r.val := fun h=> ne (Subtype.ext h)
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have force {i j : X.V} (ij : i.val≠j.val) (iv : X.D i v=true) (io : graph X.D (insert B F) i v=false)
      (jv : X.D j v=true) (jo : graph X.D (insert B F) j v=false) : X.D i j=true := by
    obtain ⟨M,cm,im,vm,one,out⟩ := full_replay X hq small step least bad full i v iv io
    obtain ⟨N,_,jn,vn,_,out'⟩ := full_replay X hq small step least bad full j v jv jo
    have inside {a : X.V} {L : Finset ℕ} (al : a.val∈L) (vl : v.val∈L) (cap : (L\B).card≤1) (av : X.D a v=true) : a.val∈B := by
      by_contra missing
      have same := card_le_one.mp cap _ (mem_sdiff.mpr ⟨al,missing⟩) _ (mem_sdiff.mpr ⟨vl,outside⟩)
      exact loopfree X.free (by omega) v.property (same ▸ av)
    have ib := inside im vm out iv
    have jb := inside jn vn out' jv
    have jmiss : j.val∉M := fun jm => ij (card_le_one.mp (cm.incoming v vm).le _
      (mem_inN.mpr ⟨im,iv⟩) _ (mem_inN.mpr ⟨jm,jv⟩))
    obtain ⟨h,hit⟩ := card_pos.mp (show 0<(outN X.D B i).card by rw [cb.heads i ib]; decide)
    obtain ⟨hb,edge⟩ := mem_outN.mp hit
    have hmiss : h∉M := by
      intro hm
      have same := card_le_one.mp (cm.heads i im).le _ (mem_outN.mpr ⟨hm,edge⟩) _ (mem_outN.mpr ⟨vm,iv⟩)
      exact outside (same ▸ hb)
    have same := card_le_one.mp one _ (mem_sdiff.mpr ⟨hb,hmiss⟩) _ (mem_sdiff.mpr ⟨jb,jmiss⟩)
    exact same ▸ edge
  have a := force diff tv rt rv rr
  have b := force (Ne.symm diff) rv rr tv rt
  exact X.free t.val 2 (by decide) hq (.step r.property a (.step t.property b (.refl _)))

theorem collision_packet_lt {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B) (least : LastArcDistanceConflict.Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (t r v : X.V) (diff : t≠r) (tv : X.D t v=true) (rt : graph X.D (insert B F) t v=false)
    (rv : X.D r v=true) (rr : graph X.D (insert B F) r v=false)
    {f g : Arc} (fm : f∈added X.D F B) (gm : g∈added X.D F B) (fg : f≠g)
    (coll : PuncturedDistance.depth X.D X.V v.val f.1=PuncturedDistance.depth X.D X.V v.val g.1) :
    (added X.D F B).card<q := by
  classical
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have vb : v.val∉B := fun mem => fg (matching cb fm gm (Or.inl (cycle_depth_injective X hq cb mem
    (mem_added.mp fm).1 (mem_added.mp gm).1 coll)))
  obtain ⟨a,af,i,ii,j,jj,edge⟩ := step.2.2
  have old : graph X.D F i j=true := active.mpr ⟨a,mem_col.mpr ⟨af,(mem_inter.mp ii).1,(mem_inter.mp jj).1,edge⟩⟩
  have tailMiss : i ∉ (added X.D F B).image Prod.fst := by
    intro hi
    obtain ⟨p,pm,eq⟩ := mem_image.mp hi
    obtain ⟨pb,qb,arc,off⟩ := mem_added.mp pm
    have h := card_le_one.mp (cb.heads i (mem_inter.mp ii).2).le _ (mem_outN.mpr ⟨qb,eq ▸ arc⟩) _
      (mem_outN.mpr ⟨(mem_inter.mp jj).2,edge⟩)
    rw [eq,h] at off
    exact Bool.noConfusion (off.symm.trans old)
  have sub : (added X.D F B).image Prod.fst ⊆ B.erase i := by
    intro s hs
    exact mem_erase.mpr ⟨fun eq => tailMiss (eq ▸ hs),by obtain ⟨p,h,rfl⟩ := mem_image.mp hs; exact (mem_added.mp h).1⟩
  have cap := card_le_card sub
  rw [card_image_of_injOn (fun a am b bm eq => matching cb am bm (Or.inl eq)),card_erase_of_mem (mem_inter.mp ii).2,cb.size] at cap
  by_contra! large
  have full : (added X.D F B).card=q := by omega
  exact diff (outside_unique_parent X hq small step least bad full t r v vb tv rt rv rr)

/-- All payments refer to the family before B was attached. The test
ranges over old duals and only over newly added arcs off the named pivot. -/
def Resolved {q n} (X : Model q n) (F : Family) (w : ℕ→ℚ) (d : ℚ) (s t z v : ℕ) : Prop :=
  graph X.D F s t=true ∧ d-1+(q:ℚ)*w v ≤ ((q:ℚ)-1)*w t ∧
  ∃ L, Cycle X.D X.V q L ∧ s∈L ∧ t∈L ∧ z∈L ∧ v∉L ∧ (L∈F ∨ Boundary X F L) ∧
    (∀ j,graph X.D (insert L F) s j=graph X.D F s j) ∧
    (∀ i,graph X.D (insert L F) i t=graph X.D F i t) ∧
    (SmallRow q (graph X.D (insert L F)) X.V ↔ ∃ p,RealDual q (graph X.D F) X.V 1 p ∧
      ∀ a∈L,∀ b∈L,a≠s → b≠t → b≠v → X.D a b=true → graph X.D F a b=false →
        realCol q (graph X.D F) X.V p b+q*p a≤1)

theorem resolve_orientation {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B) (least : LastArcDistanceConflict.Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    {w ρ d} (flat : OmittedCycleProgress.Flat q (graph X.D (insert B F)) X.V w ρ d)
    (r t v : X.V) (ne : r≠t) (rv : X.D r v=true) (off : graph X.D (insert B F) r v=false)
    (tv : X.D t v=true) {f g : Arc} (fm : f∈added X.D F B) (gm : g∈added X.D F B) (fg : f≠g)
    (coll : PuncturedDistance.depth X.D X.V v.val f.1=PuncturedDistance.depth X.D X.V v.val g.1)
    (pivot : Priced X (graph X.D (insert B F)) w r t r) {z} (zv : z∈X.V)
    (other : Priced X (graph X.D (insert B F)) w z r t) : Resolved X F w d r t z v := by
  classical
  have base := parent_arc_in_base X hq small step least bad r v rv off fm gm fg coll r.property rv pivot.oldArc
  have cost := merge_price X (fun _ _ h=>CrossValueOmissions.selected_sub h) flat r.property v.property rv off pivot
  obtain ⟨L,cl,zl,rl,tl⟩ := SaturatedCycleClasses.missing hq X.free X.sat zv r.property t.property
    (CrossValueOmissions.selected_sub other.oldArc) (CrossValueOmissions.selected_sub base) (by simp [other.misses])
  have vl : v.val∉L := fun mem => ne (Subtype.ext (card_le_one.mp (cl.incoming v mem).le _
    (mem_inN.mpr ⟨rl,rv⟩) _ (mem_inN.mpr ⟨tl,tv⟩)))
  have place : L∈F ∨ Boundary X F L := by
    by_cases inside : L∈F
    · exact Or.inl inside
    obtain ⟨A,hit⟩ := active.mp base
    obtain ⟨af,ra,ta,edge⟩ := mem_col.mp hit
    exact Or.inr ⟨mem_filter.mpr ⟨mem_powerset.mpr cl.sub,cl⟩,inside,A,af,r.val,
      mem_inter.mpr ⟨ra,rl⟩,t.val,mem_inter.mpr ⟨ta,tl⟩,edge⟩
  obtain ⟨row,col,_,bills⟩ := original_bills X cl rl tl vl base
  refine ⟨base,cost,L,cl,rl,tl,zl,vl,place,row,col,?_⟩
  constructor
  · intro paid
    obtain ⟨p,hp⟩ := realDual_of_smallRow paid X.live
    have prior : RealDual q (graph X.D F) X.V 1 p := by
      refine ⟨hp.nonneg,hp.normalized,fun j jv => le_trans ?_ (hp.columns j jv)⟩
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
      apply sum_le_sum
      intro i iv
      by_cases edge : graph X.D F i j=true
      · have keep : graph X.D (insert L F) i j=true := union_arc.mpr (Or.inl edge)
        simp [edge,keep]
      · cases graph X.D (insert L F) i j <;> simp [edge,hp.nonneg i iv]
    exact ⟨p,prior,(bills p prior).mp hp⟩
  · rintro ⟨p,hp,fit⟩
    exact smallRow_of_realDual ((bills p hp).mpr fit)

def GateLaw {q n} (X : Model q n) (F : Family) (B : Finset ℕ) : Prop :=
  ∀ w ρ d, OmittedCycleProgress.Flat q (graph X.D (insert B F)) X.V w ρ d →
  ∀ t r v : X.V,t≠r → X.D t v=true → graph X.D (insert B F) t v=false →
    X.D r v=true → graph X.D (insert B F) r v=false →
  ∀ f∈added X.D F B,∀ g∈added X.D F B,f≠g →
    PuncturedDistance.depth X.D X.V v.val f.1=PuncturedDistance.depth X.D X.V v.val g.1 →
    (added X.D F B).card<q ∧ ∃ y∈X.V, ∃ z∈X.V, y≠z ∧
      Priced X (graph X.D (insert B F)) w y t r ∧ Priced X (graph X.D (insert B F)) w z r t ∧
      (y=r.val → Resolved X F w d r t z v) ∧ (z=t.val → Resolved X F w d t r y v)

theorem at_gate {q n F B} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (step : Boundary X F B) (least : LastArcDistanceConflict.Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) : GateLaw X F B := by
  intro w ρ d flat t r v tr tv ot rv ort f fm g gm fg coll
  have sub (i j) (h : graph X.D (insert B F) i j=true) := CrossValueOmissions.selected_sub h
  have diff : t.val≠r.val := fun e=>tr (Subtype.ext e)
  obtain ⟨y,yv,yp⟩ := priced_parent X small sub flat t.property r.property diff
  obtain ⟨z,zv,zp⟩ := priced_parent X small sub flat r.property t.property (Ne.symm diff)
  have yz : y≠z := fun e=>Bool.noConfusion ((sub y t yp.oldArc).symm.trans (e ▸ zp.misses))
  refine ⟨collision_packet_lt X hq small step least bad t r v tr tv ot rv ort fm gm fg coll,y,yv,z,zv,yz,yp,zp,?_,?_⟩
  · intro eq
    exact resolve_orientation X hq small step least bad flat r t v (Ne.symm tr) rv ort tv fm gm fg coll (eq ▸ yp) zv zp
  · intro eq
    exact resolve_orientation X hq small step least bad flat t r v tr tv ot rv fm gm fg coll (eq ▸ zp) yv yp

def OnModel {q n} (X : Model q n) : Prop :=
  ∀ F B, Boundary X F B → LastArcDistanceConflict.Minimum X F B →
    ¬SmallRow q (graph X.D (insert B F)) X.V → GateLaw X F B

theorem on_model {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card) : OnModel X :=
  fun _ _ step least bad => at_gate X hq small step least bad

#print axioms original_bills
#print axioms no_late_tail
#print axioms parent_arc_in_base
#print axioms collision_packet_lt
#print axioms outside_unique_parent
#print axioms at_gate
#print axioms on_model
#print axioms resolve_orientation
#print axioms priced_parent
#print axioms merge_price
end LeanCH.BR.Closure.LastArcMergePayment
