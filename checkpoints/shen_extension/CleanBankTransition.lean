import checkpoints.shen_extension.BankFiveCommonHeads

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- The bounded conflict graph of a three-label bank. Only covering rows
with a head in the original bank can spoil the swap. -/
def LocalSwapStatement : Prop :=
  ∀ {D : CH.Digraph} {B T : Finset ℕ} {d : ℕ}, B.card=3 → Disjoint B T → d∈T →
    QFree D (B∪T) 3 → (∀ b∈B, D b d ≠ true) →
    (∀ u∈T, (outN D B u).card=1) → (∀ b∈B, (inN D (B∪T) b).card ≤ 2) →
    ∃ u∈T, (u=d ∨ D u d=true ∨ ∃ v∈T, D u v=true ∧ D v d=true) ∧
      ∃ k∈B, ∀ y∈(B∪T) \ insert u (B.erase k), (outN D (insert u (B.erase k)) y).card ≤ 1

/-- Transfer a clean swap from the bounded conflict graph to the original
carrier, preserving the selected target set and excluding all three-hit rows. -/
theorem transfer_clean_swap (law : LocalSwapStatement) {D : CH.Digraph} {V B P : Finset ℕ} {c d : ℕ}
    (safe : QFree D V 3) (bv : B ⊆ V) (three : B.card=3) (pv : P ⊆ V)
    (common : ∀ b ∈ B, P ⊆ outN D V b) (cap : TripleCap D V P.card)
    (cu : c ∈ V \ B) (allB : B ⊆ outN D V c) (miss : ∃ z∈P, D c z ≠ true)
    (lone : ∀ v ∈ V \ B, v ≠ c → (outN D B v).card ≤ 1)
    (du : d ∈ V \ B) (dp : P ⊆ outN D V d) (dc : D d c=true)
    (heads : outN D (V \ B) c ⊆ outN D V d) (hit : (outN D B d).Nonempty) :
    ∃ k∈B, ∃ u∈V\B, let B' := insert u (B.erase k)
      B' ⊆ V ∧ B'.card=3 ∧ (∀ b∈B', P ⊆ outN D V b) ∧
      (∀ v∈V\B', (outN D B' v).card ≤ 2) ∧
      (∀ v∈V\B', 2 ≤ (outN D B' v).card → ∃ z∈P, D v z ≠ true) := by
  classical
  let W := V.filter (fun v => P ⊆ outN D V v)
  let T := (W \ B).filter (fun v => (outN D B v).Nonempty)
  have wv : W ⊆ V := filter_subset ..
  have bw : B ⊆ W := fun b bb => mem_filter.mpr ⟨bv bb,common b bb⟩
  have tw : T ⊆ W := fun v m => (mem_sdiff.mp (mem_filter.mp m).1).1
  have extT {v} (m : v∈T) : v∈V\B := mem_sdiff.mpr ⟨wv (tw m),(mem_sdiff.mp (mem_filter.mp m).1).2⟩
  have both : B∪T ⊆ V := union_subset bv (tw.trans wv)
  have allW : B∪T ⊆ W := union_subset bw tw
  have cw : c ∉ W := by
    obtain ⟨p,pm,off⟩ := miss
    exact fun m => off (mem_outN.mp ((mem_filter.mp m).2 pm)).2
  have dT : d∈T := mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨(mem_sdiff.mp du).1,dp⟩,
    (mem_sdiff.mp du).2⟩,hit⟩
  have inc (b) (bb : b∈B) : (inN D (B∪T) b).card ≤ 2 := by
    by_contra! large
    obtain ⟨x,xm,y,ym,z,zm,xy,xz,yz⟩ := two_lt_card.mp large
    have cond {v} (m : v∈inN D (B∪T) b) : insert b P ⊆ outN D V v :=
      insert_subset (mem_outN.mpr ⟨bv bb,(mem_inN.mp m).2⟩)
        (mem_filter.mp (allW (mem_inN.mp m).1)).2
    have lim := (card_le_card (subset_inter (subset_inter (cond xm) (cond ym)) (cond zm))).trans
      (cap x y z (both (mem_inN.mp xm).1) (both (mem_inN.mp ym).1) (both (mem_inN.mp zm).1) xy xz yz)
    have bp : b∉P := fun m => loopfree safe (by decide) (bv bb) (mem_outN.mp (common b bb m)).2
    rw [card_insert_of_notMem bp] at lim
    omega
  have dcOff (b) (bb : b∈B) : D b d ≠ true := fun bd => safe b 3 (by decide) (by decide)
    (.step (mem_sdiff.mp du).1 bd (.step (mem_sdiff.mp cu).1 dc (.step (bv bb) (mem_outN.mp (allB bb)).2 (.refl _))))
  have col (v) (m : v∈T) : (outN D B v).card=1 := by
    have bound := lone v (extT m) (fun e => cw (e ▸ tw m))
    have pos := card_pos.mpr (mem_filter.mp m).2
    omega
  have dis : Disjoint B T := disjoint_left.mpr (fun v vb vt => (mem_sdiff.mp (extT vt)).2 vb)
  obtain ⟨u,ut,reach,k,kb,clean⟩ := law three dis dT (safe.mono_set both) dcOff col inc
  have uU := extT ut
  have uc : D c u ≠ true := by
    intro e
    rcases reach with eq | direct | ⟨v,vt,first,last⟩
    · exact digonfree safe (by decide) (mem_sdiff.mp du).1 (mem_sdiff.mp cu).1 dc (eq ▸ e)
    · exact safe c 3 (by decide) (by decide) (.step (wv (tw ut)) e
        (.step (mem_sdiff.mp du).1 direct (.step (mem_sdiff.mp cu).1 dc (.refl _))))
    · have head := (mem_outN.mp (heads (mem_outN.mpr ⟨uU,e⟩))).2
      exact safe d 3 (by decide) (by decide) (.step (wv (tw ut)) head
        (.step (wv (tw vt)) first (.step (mem_sdiff.mp du).1 last (.refl _))))
  let B' := insert u (B.erase k)
  have ub := (mem_sdiff.mp uU).2
  have b'v : B' ⊆ V := insert_subset (wv (tw ut)) ((erase_subset ..).trans bv)
  have num : (B.erase k).card=2 := by have n := card_erase_add_one kb; omega
  have nB : B'.card=3 := by
    change (insert u (B.erase k)).card=3
    rw [card_insert_of_notMem (fun m => ub (mem_erase.mp m).2),num]
  have covers (x) (xm : x∈B') : P ⊆ outN D V x := by
    rcases mem_insert.mp xm with rfl | be
    · exact (mem_filter.mp (tw ut)).2
    · exact common _ (mem_erase.mp be).2
  have headIncl (v) : outN D B' v ⊆ insert u (outN D B v) := by
    intro w wm
    obtain ⟨wb,edge⟩ := mem_outN.mp wm
    rcases mem_insert.mp wb with eq | be
    · exact mem_insert.mpr (Or.inl eq)
    · exact mem_insert_of_mem (mem_outN.mpr ⟨(mem_erase.mp be).2,edge⟩)
  have outer (v) (vv : v∈V\B') (vw : v∈W) : (outN D B' v).card ≤ 1 := by
    by_cases m : v∈B∪T
    · exact clean v (mem_sdiff.mpr ⟨m,(mem_sdiff.mp vv).2⟩)
    have vb : v∉B := fun h => m (mem_union_left _ h)
    have empty : outN D B v=∅ := not_nonempty_iff_eq_empty.mp
      (fun h => m (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨vw,vb⟩,h⟩)))
    have le := card_le_card (headIncl v)
    rw [empty] at le
    simpa using le
  refine ⟨k,kb,u,uU,b'v,nB,covers,?_,?_⟩
  · intro v vv
    by_cases vw : v∈W
    · exact (outer v vv vw).trans (by decide)
    have vb : v∉B := fun m => vw (bw m)
    by_cases vc : v=c
    · subst v
      have incl : outN D B' c ⊆ B.erase k := fun w m => (mem_insert.mp (outN_subset m)).resolve_left
        (fun e => uc (e ▸ (mem_outN.mp m).2))
      exact (card_le_card incl).trans num.le
    have l := lone v (mem_sdiff.mpr ⟨(mem_sdiff.mp vv).1,vb⟩) vc
    have le := card_le_card (headIncl v)
    have n := card_insert_le u (outN D B v)
    change (outN D B' v).card ≤ 2
    omega
  · intro v vv short
    by_contra! all
    have vm : v∈W := mem_filter.mpr ⟨(mem_sdiff.mp vv).1,fun p pp => mem_outN.mpr ⟨pv pp,all p pp⟩⟩
    have lim := outer v vv vm
    change 2 ≤ (outN D B' v).card at short
    omega


/-- A tight parent receiving an arc from every other parent can send no
arc outside the neutral set and c. A return to a parent would be a
two-cycle or a triangle through the receiving parent. -/
theorem receiving_parent_row {D : CH.Digraph} {U H L : Finset ℕ} {c d t : ℕ}
    (safe : QFree D U 3) (hu : H ⊆ U) (dm : d∈H) (dc : D d c=true) (cu : c∈U)
    (incoming : ∀ h∈H, h≠d → D h d=true)
    (neut : neutral D U H c = L) (sat : L.card+1=t)
    (degree : (outN D U d).card=t) : (outN D U d).erase c=L := by
  classical
  have incl : (outN D U d).erase c ⊆ L := by
    intro v vm
    obtain ⟨vc,hv⟩ := mem_erase.mp vm
    obtain ⟨vu,dv⟩ := mem_outN.mp hv
    have vd : v≠d := fun e => loopfree safe (by decide) (hu dm) (e ▸ dv)
    have back := digonfree safe (by decide) (hu dm) vu dv
    rw [←neut]
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨vc,vu⟩,fun vh => back (incoming v vh vd)⟩,?_⟩
    apply disjoint_left.mpr
    intro h edge hm
    by_cases eq : h=d
    · exact back (eq ▸ (mem_outN.mp edge).2)
    · exact safe d 3 (by decide) (by decide)
        (.step vu dv (.step (hu hm) (mem_outN.mp edge).2 (.step (hu dm) (incoming h hm eq) (.refl _))))
  have n := card_erase_add_one (mem_outN.mpr ⟨cu,dc⟩ : c∈outN D U d)
  exact eq_of_subset_of_card_le incl (by omega)

/-- On the lone three-parent branch, the hypotheses on the distinguished
covering row d needed for the clean swap come from the sink's actual row. -/
theorem bank_clean_two_hits (law : LocalSwapStatement) {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 7 ≤ s) (order : V.card=3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (bv : B ⊆ V) (three : B.card=3) (pv : P ⊆ V)
    (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b) (cap : TripleCap D V P.card)
    (cu : c∈V\B) (hits : (outN D B c).card=3)
    (lone : ∀ v∈V\B, v≠c → (outN D B v).card ≤ 1)
    (menu : (rowMenu D (V\B) P c).card ≤ 1) (miss : ∃ z∈P, D c z≠true)
    (shape : (tightParents D (V\B) c (s-1)).card=3 ∨
      ∃ d∈tightParents D (V\B) c (s-1), ∀ h∈tightParents D (V\B) c (s-1), h≠d → D h d=true) :
    ∃ k∈B, ∃ u∈V\B, let B' := insert u (B.erase k)
      B'⊆V ∧ B'.card=3 ∧ (∀ b∈B', P⊆outN D V b) ∧
      (∀ v∈V\B', (outN D B' v).card ≤ 2) ∧
      (∀ v∈V\B', 2≤(outN D B' v).card → ∃ z∈P, D v z≠true) ∧
      2 ≤ ((V\B').filter (fun v => 2≤(outN D B' v).card)).card := by
  classical
  let U := V\B
  let t := s-1
  have uv : U⊆V := sdiff_subset
  have size : U.card=3*t := by
    change (V\B).card=3*(s-1); rw [card_sdiff_of_subset bv,order,three]; omega
  obtain ⟨z,zp,cz,sat,ne,_,rest,j,_,_,ju,cj,spare⟩ :=
    bank_saturation safe reg (by omega) order no bv three pv many common cu hits lone menu miss
  let L := insert z (outN D U c)
  change neutral D U (tightParents D U c t) c = L at ne
  have hrow : ∃ d∈tightParents D U c t, (outN D U d).erase c=L := by
    rcases shape with eq3 | ⟨d,dm,receive⟩
    · obtain ⟨a,b,d,_,_,_,triple,_,_,drow,_⟩ :=
        three_parent_structure (safe.mono_set uv) cu ju cj size.le no rest
          (fun w wm => by rw [spare w wm]; dsimp [t]; omega) sat ne.ge eq3
      exact ⟨d,by rw [triple]; simp,drow⟩
    · obtain ⟨par,low⟩ := mem_filter.mp dm
      obtain ⟨du,dc⟩ := mem_inN.mp par
      have nc : d≠c := fun eq => loopfree safe (by decide) (uv du) (eq ▸ dc)
      exact ⟨d,dm,receiving_parent_row (safe.mono_set uv)
        (fun _ m => (mem_inN.mp (mem_filter.mp m).1).1) dm dc cu receive ne sat
        (le_antisymm low (rest d du nc))⟩
  obtain ⟨d,dm,drow⟩ := hrow
  obtain ⟨pred,low⟩ := mem_filter.mp dm
  obtain ⟨du,dc⟩ := mem_inN.mp pred
  have bankRow := card_outN_union (D:=D) (show Disjoint B U from disjoint_sdiff) d
  rw [union_sdiff_of_subset bv,reg _ (uv du)] at bankRow
  have pos : (outN D B d).Nonempty := card_pos.mp (by change (outN D U d).card ≤ s-1 at low; omega)
  have dL {r} (rl : r∈L) : r∈outN D V d := by
    have m : r∈(outN D U d).erase c := by rw [drow]; exact rl
    have h := mem_outN.mp (mem_erase.mp m).2
    exact mem_outN.mpr ⟨uv h.1,h.2⟩
  have incl : P ⊆ L := by
    intro r rp
    by_cases e : D c r=true
    · have ru : r∈U := mem_sdiff.mpr ⟨pv rp,fun rb => loopfree safe (by decide)
        (pv rp) (mem_outN.mp (common r rb rp)).2⟩
      exact mem_insert_of_mem (mem_outN.mpr ⟨ru,e⟩)
    have unhit {v} (vp : v∈P) (cv : D c v≠true) : v∈rowMenu D U P c :=
      mem_union_left _ (mem_sdiff.mpr ⟨vp,fun h => cv (mem_outN.mp h).2⟩)
    have eq := card_le_one.mp menu r (unhit rp e) z (unhit zp cz)
    exact eq ▸ mem_insert_self ..
  have all : outN D B c=B := eq_of_subset_of_card_le outN_subset (by omega)
  have allB : B ⊆ outN D V c := fun v vm => mem_outN.mpr ⟨bv vm,
    (mem_outN.mp (show v ∈ outN D B c by rw [all]; exact vm)).2⟩
  obtain ⟨k,kb,u,uu,sub,size',cov,maxTwo,clean⟩ := transfer_clean_swap law safe bv three pv common cap
    cu allB miss lone du (fun _ m => dL (incl m)) dc (fun _ m => dL (mem_insert_of_mem m)) pos
  let B' := insert u (B.erase k)
  have result := repair_on_triple safe reg hs order no pv sub size' cov clean
  refine ⟨k,kb,u,uu,sub,size',cov,maxTwo,clean,?_⟩
  rcases result.2.2 with several | ⟨v,one,all,_⟩
  · exact several
  · have vm : v ∈ (V\B').filter (fun w => 2≤(outN D B' w).card) := one ▸ mem_singleton_self _
    have bad := maxTwo v (mem_filter.mp vm).1
    omega

/-- The top-order selection can bypass a lone three-parent survivor
or a parent receiving all other parents, using the local finite swap. -/
theorem select_several_or_four (law : LocalSwapStatement) {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 8≤s) (order : V.card=3*s)
    (no : BypassRepair.NoHost 3 (s-1)) :
    ∃ P ⊆ V, 2 ≤ P.card ∧ TripleCap D V P.card ∧ ∃ B ⊆ V, B.card=3 ∧
      (∀ b∈B, P⊆outN D V b) ∧
      let U := V\B
      let S := U.filter (fun c => 2≤(outN D B c).card)
      (∀ c∈S, ∃ z∈P, D c z≠true) ∧
      (2≤S.card ∨ ∃ c, S={c} ∧ (outN D B c).card=3 ∧ (rowMenu D U P c).card=1 ∧
        4≤(tightParents D U c (s-1)).card ∧ ∀ d∈tightParents D U c (s-1),
          ∃ h∈tightParents D U c (s-1), h≠d ∧ D h d≠true) := by
  classical
  obtain ⟨P,pv,many,cap,B,bv,three,common,miss,front⟩ := selected_moment_frontier safe reg hs order no
  refine ⟨P,pv,many,cap,?_⟩
  rcases front with several | ⟨c,one,hits,menu,parent⟩
  · exact ⟨B,bv,three,common,miss,Or.inl several⟩
  have cs : c∈(V\B).filter (fun x => 2≤(outN D B x).card) := one ▸ mem_singleton_self _
  have lone (v) (vu : v∈V\B) (ne : v≠c) : (outN D B v).card≤1 := by
    by_contra! bad
    exact ne (mem_singleton.mp (one ▸ (mem_filter.mpr ⟨vu,by omega⟩)))
  let H := tightParents D (V\B) c (s-1)
  by_cases shape : H.card=3 ∨ ∃ d∈H, ∀ h∈H, h≠d → D h d=true
  case neg =>
    have four : 4≤H.card := parent.elim id (fun h => False.elim (shape (Or.inl h.1)))
    have missed : ¬ ∃ d∈H, ∀ h∈H, h≠d → D h d=true := fun r => shape (Or.inr r)
    push Not at missed
    exact ⟨B,bv,three,common,miss,Or.inr ⟨c,one,hits,menu,four,missed⟩⟩
  obtain ⟨k,_,u,_,sub,num,cov,_,clean,high⟩ := bank_clean_two_hits law safe reg (by omega) order no
    bv three pv many common cap (mem_filter.mp cs).1 hits lone menu.le (miss c cs) shape
  exact ⟨insert u (B.erase k),sub,num,cov,(fun _ m => clean _ (mem_filter.mp m).1 (mem_filter.mp m).2),Or.inl high⟩

#print axioms bank_clean_two_hits
#print axioms select_several_or_four

#print axioms receiving_parent_row
#print axioms transfer_clean_swap
end LeanCH.BR.TripleBank
