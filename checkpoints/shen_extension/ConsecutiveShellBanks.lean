import checkpoints.shen_extension.RetainedLayerOrders

namespace LeanCH.BR.ConsecutiveShellBanks
open Finset BRq2 BRq3 BR45 BRsGen OneSpareGrowth BankReachTransfer

/-- Two successive layers of size r−1. The rows with one internal head
are physical witnesses, each with its own two- and three-step balls. -/
theorem full_rows {D V q r u k} (free : QFree D V q) (hq : 4≤q) (root : u∈V)
    (reg : OutEq r D V) (hr : 2≤r) (time : k+3≤q) (pressure : r≤q+k+1)
    (ys : (N2 D V u).card+1=r) (zs : (N3 D V u).card+1=r) :
    let X := outN D V u
    let F := X.filter (fun w=>(outN D X w).card=1)
    2*q+2≤r+F.card ∧ ∀w∈F,
      2*r+1≤(ball D V w 2).card ∧ 3*r+1≤(ball D V w 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4 \ ball D V u 3
  have xd : X.card=r := reg u root
  have xy : Disjoint X Y := disjXY
  have yz : Disjoint Y Z := disjoint_left.mpr (fun _ ym zm=>(mem_N3.mp zm).2 (mem_N2.mp ym).1)
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have native x (xm : x∈V) := hr.trans (reg x xm).ge
  have sizeX : X.card≤2*q := by omega
  have positive x (xm : x∈X) := internal_positive free hq root reg ys xm
  have supply := LocalBallTransfer.light_supply (free.mono_set xv) (by omega)
    (card_pos.mp (by omega : 0<X.card)) positive sizeX
  have moves := reaches_bank free (by omega) xv yv xy native
    (fun x xm=> by rw [←outN_X_eq (free.mono_bound hq) root xm,reg x (xv xm)]; exact ys.le)
    sizeX (by omega : k≤q) (by omega)
  have headsY (y) (ym : y∈Y) : outN D V y⊆outN D (Y∪Z) y := by
    intro z zm
    obtain ⟨zV,arc⟩ := mem_outN.mp zm
    apply mem_outN.mpr
    refine ⟨?_,arc⟩
    rcases headY (free.mono_bound hq) root ym zV arc with hit|last
    · rcases mem_union.mp hit with xx|yy
      · obtain ⟨j,_,fit,path⟩ := moves z xx y ym
        exact (free z _ (by omega) (by omega) (path.snoc zV arc)).elim
      · exact mem_union_left _ yy
    · exact mem_union_right _ last
  have next := reaches_bank free (by omega) yv zv yz native
    (fun y ym=>zs.le.trans ((reg y (yv ym)).ge.trans (card_le_card (headsY y ym))))
    (by dsimp [Y]; omega) (by omega : k≤q)
    (by dsimp [Y]; omega)
  have reachZ (x) (xm : x∈X) (z) (zm : z∈Z) : ∃l,0<l ∧ l≤k+2 ∧ Walk D V x z l := by
    obtain ⟨p,pb,arc⟩ := ball_succ_pred root (mem_N3.mp zm).1 (mem_N3.mp zm).2
    have py : p∈Y := mem_sdiff.mpr ⟨pb,fun early=>(mem_N3.mp zm).2 (ball_step early (zv zm) arc)⟩
    obtain ⟨j,pos,le,road⟩ := moves x xm p py
    exact ⟨j+1,by omega,by omega,road.snoc (zv zm) arc⟩
  have bound : r≤W.card+1 := by
    by_contra! low
    have inner (z) (zm : z∈Z) : 2≤(outN D Z z).card := by
      have sub : outN D V z⊆outN D Z z∪W := by
        intro x hit
        obtain ⟨xv',zx⟩ := mem_outN.mp hit
        have fourth := ball_step (mem_N3.mp zm).1 xv' zx
        by_cases third : x∈ball D V u 3
        · by_cases two : x∈ball D V u 2
          · by_cases one : x∈ball D V u 1
            · rcases (mem_ball_one root).mp one with rfl|xx
              · exact (no_back_arc free root (mem_N3.mp zm).1 (by omega) zx).elim
              · obtain ⟨l,_,fit,path⟩ := reachZ x xx z zm
                exact (free x _ (by omega) (by omega) (path.snoc xv' zx)).elim
            · obtain ⟨l,_,fit,path⟩ := next x (mem_sdiff.mpr ⟨two,one⟩) z zm
              exact (free x _ (by omega) (by omega) (path.snoc xv' zx)).elim
          · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨third,two⟩,zx⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨fourth,third⟩)
      have count := (card_le_card sub).trans (card_union_le _ _)
      rw [reg z (zv zm)] at count
      omega
    have zpos : Z.Nonempty := card_pos.mp (by dsimp [Z]; omega)
    have limit := corB (by omega : 1≤q) (free.mono_set zv) inner zpos
    dsimp [Z] at limit
    omega
  refine ⟨by simpa only [xd] using supply,?_⟩
  intro w wm
  obtain ⟨wx,one⟩ := mem_filter.mp wm
  have covers := sends_layer free hq root reg ys wx one
  have seen : ball D V u 2 \ ball D V u 1 ⊆ ball D V w 1 := fun y ym=>
    (mem_ball_one (xv wx)).mpr (Or.inr (mem_outN.mpr ⟨yv ym,covers y ym⟩))
  have total (j) (jp : 0<j) (dist : j+1≤q) : j+1+(ball D V u (1+1+(j-1))).card-(ball D V u 1).card
       ≤ (ball D V w (1+(j-1))).card := by
    have sub : ball D X w j ⊆ ball D V u 1 := fun a am=>X_B1 (ball_subset am)
    have grow := ball_one_growth (free.mono_set xv) positive wx j dist
    have jj : j=1+(j-1) := by omega
    have inside : ball D X w j ⊆ ball D V w (1+(j-1)) := by
        rw [←jj]
        intro a am
        obtain ⟨ax,l,le,path⟩ := mem_ball.mp am
        exact mem_ball.mpr ⟨xv ax,l,le,path.mono xv⟩
    have add := count_with_prefix (k:=j-1) root sub inside seen
    have mono := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by omega : 1≤1+1+(j-1)))
    omega
  have a := total 2 (by decide) (by omega)
  have b := total 3 (by decide) (by omega)
  simp only [Nat.reduceAdd,Nat.reduceSub] at a b
  have shell := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
  change W.card+_= _ at shell
  have two := @card_B2 D V u
  have three := @card_B3 D V u
  omega

/-- If two short roots use a common full row then both directions miss.
Keep the same physical witnesses for the row count and for the pair count. -/
theorem supply {D V q r k} {S : Finset ℕ} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (hr : 2≤r) (time : k+3≤q) (pressure : r≤q+k+1)
    (sub : S⊆V) (shape : ∀u∈S,(N2 D V u).card+1=r ∧ (N3 D V u).card+1=r)
    {T : Finset ℕ}
    (eligible : ∀w∈V,2*r+1≤(ball D V w 2).card → 3*r+1≤(ball D V w 3).card → w∈T) :
    ∃g,g≤S.card ∧ (S.Nonempty → 0<g) ∧ g*(2*q+2-r)≤T.card ∧
      2*(S.card-g)≤(DotClonePairCompletion.orderedIncomparable D V q).card := by
  classical
  let F := fun u => (outN D V u).filter (fun w=>(outN D (outN D V u) w).card=1)
  have witness u (um : u∈S) := full_rows free hq (sub um) reg hr time pressure (shape u um).1 (shape u um).2
  have paid u (um : u∈S) : 2*q+2-r≤(F u).card := by
    have h := (witness u um).1
    change 2*q+2≤r+(F u).card at h
    omega
  have misses u (um : u∈S) v (vm : v∈S) (diff : u≠v) w (wu : w∈F u) (wv : w∈F v) :
      v∉ball D V u q := by
    obtain ⟨ux,uo⟩ := mem_filter.mp wu
    obtain ⟨vx,vo⟩ := mem_filter.mp wv
    exact SharedLayerBarrier.shared_full_remote free hq (sub um) (sub vm) diff reg
      (shape u um).1 (shape v vm).1 ux vx
      (sends_layer free hq (sub um) reg (shape u um).1 ux uo)
      (sends_layer free hq (sub vm) reg (shape v vm).1 vx vo)
  apply SharedBankLedger.witness_budget F paid
  · intro u um w fw
    have ⟨a,b⟩ := (witness u um).2 w fw
    exact eligible w (outN_subset (mem_filter.mp fw).1) a b
  · intro u um v vm ne w wu wv
    exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨sub um,sub vm,ne⟩,misses u um v vm ne w wu wv,
      misses v vm u um ne.symm w wv wu⟩

/-- Space left by missed ordered pairs applies also to unequal radii. -/
theorem remote_capacity {D V q i j} (free : QFree D V q) (time : i+j≤q) :
    (DotClonePairCompletion.orderedIncomparable D V q).card +
      (∑x∈V, ((ball D V x i).card+(ball D V x j).card))≤V.card*(V.card+1) := by
  classical
  have part (x) (xm : x∈V) :
      (V \ (ball D V x q ∪ reverseBall D V x q)).card+
      ((ball D V x i).card+(reverseBall D V x j).card)≤V.card+1 := by
    let A := ball D V x i
    let B := reverseBall D V x j
    have ab : A∩B ⊆ {x} := by
      intro y ym
      have ret := reverseBall_subset_complement (v:=x) free time (mem_inter.mp ym).2
      rcases mem_union.mp ret with off|eq
      · exact ((mem_sdiff.mp off).2 (mem_inter.mp ym).1).elim
      · exact eq
    have sub : A∪B⊆V := union_subset ball_subset (filter_subset _ _)
    have into : A∪B⊆ball D V x q ∪ reverseBall D V x q := by
      apply union_subset_union (ball_mono_radius (by omega))
      intro y ym
      obtain ⟨yv,path⟩ := mem_filter.mp ym
      exact mem_filter.mpr ⟨yv, ball_mono_radius (by omega : j≤q) path⟩
    have card := card_le_card (show V \ (ball D V x q ∪ reverseBall D V x q) ⊆ V \ (A∪B) from fun _ m=>mem_sdiff.mpr ⟨(mem_sdiff.mp m).1,fun a=>(mem_sdiff.mp m).2 (into a)⟩)
    have a := card_union_add_card_inter A B
    have b := card_sdiff_add_card_eq_card sub
    have c := card_le_card ab
    rw [card_singleton] at c
    change _+(A.card+B.card)≤_ 
    omega
  have sum := sum_le_sum part
  rw [sum_add_distrib,sum_add_distrib,sum_const_nat (fun _ _=>rfl),sum_reverseBall_eq_sum_ball] at sum
  rw [DotClonePairCompletion.incomparable_card_rows,sum_add_distrib]
  exact sum

/-- Generic counting step. Each short row can cost at most two ordered
slots, and each high row pays two. A pair of mutually remote short rows
contributes two labelled, unused slots. -/
theorem no_short_bank {V S T : Finset ℕ} {score : ℕ→ℕ} {base missed d : ℕ}
    (sv : S⊆V) (tv : T⊆V) (apart : Disjoint S T)
    (short : ∀x∈S,base≤score x+2) (ordinary : ∀x∈V\S,base≤score x)
    (high : ∀x∈T,base+2≤score x) (cap : missed+(∑x∈V,score x)≤V.card*base)
    (supply : ∃g,g≤S.card ∧ (S.Nonempty → 0<g) ∧ g*d≤T.card ∧ 2*(S.card-g)≤missed)
    (many : 2≤d) : S=∅ := by
  by_contra ne
  obtain ⟨g,gs,pos,rows,holes⟩ := supply
  have gp := pos (nonempty_iff_ne_empty.mpr ne)
  have count := (Nat.mul_le_mul_left g many).trans rows
  have off : T⊆V\S := fun x xm=>mem_sdiff.mpr ⟨tv xm,fun xs=>disjoint_left.mp apart xs xm⟩
  have paidS := sum_le_sum short
  have paidT := RetainedRadiusLayers.add_layer (f:=fun _=>base) (g:=score) off ordinary high
  rw [sum_const_nat (fun _ _=>rfl),sum_add_distrib,sum_const_nat (fun _ _=>rfl)] at paidS
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset sv] at paidT
  have merge := sum_sdiff sv (f:=score)
  have split : (V.card-S.card)*base+S.card*base=V.card*base := by
    rw [←Nat.add_mul,Nat.sub_add_cancel (card_le_card sv)]
  omega

attribute [aesop safe forward (immediate := [free,hq,root,reg,hr,time,pressure,ys,zs])
  (rule_sets := [CHGraphFamilies])] full_rows
attribute [aesop safe forward (immediate := [free,hq,reg,hr,time,pressure,sub,shape,eligible])
  (rule_sets := [CHGraphFamilies])] supply
attribute [aesop safe forward (immediate := [free,time]) (rule_sets := [CHGraphFamilies])] remote_capacity
attribute [aesop safe forward (immediate := [sv,tv,apart,short,ordinary,high,cap,supply,many])
  (rule_sets := [CHGraphFamilies])] no_short_bank

/-- Once a low-score root has two successive layers of size r−1, all
roots below the average are excluded by charging *distinct* pairs. The
radii of the score may differ. -/
theorem paid_shells {D V q r i j k base} (free : QFree D V q) (reg : OutEq r D V)
    (hq : 4≤q) (hr : 2≤r) (time : k+3≤q) (pressure : r≤q+k+1)
    (many : 2≤2*q+2-r) (radii : i+j≤q) (ambient : V.card+1≤base)
    (floor : ∀x∈V,base≤(ball D V x i).card+(ball D V x j).card+2)
    (shape : ∀x∈V,(ball D V x i).card+(ball D V x j).card<base →
      (N2 D V x).card+1=r ∧ (N3 D V x).card+1=r)
    (bonus : ∀x∈V,2*r+1≤(ball D V x 2).card → 3*r+1≤(ball D V x 3).card →
      base+2≤(ball D V x i).card+(ball D V x j).card) :
    ∀x∈V,base≤(ball D V x i).card+(ball D V x j).card := by
  classical
  let score := fun x=>(ball D V x i).card+(ball D V x j).card
  let S := V.filter (fun x=>score x<base)
  let T := V.filter (fun x=>base+2≤score x)
  have sv : S⊆V := filter_subset _ _
  have tv : T⊆V := filter_subset _ _
  have rows := supply free hq reg hr time pressure sv
    (fun x xm=>shape x (sv xm) (mem_filter.mp xm).2)
    (T:=T) (fun x xv a b=>mem_filter.mpr ⟨xv,bonus x xv a b⟩)
  have cap := (remote_capacity free radii).trans (Nat.mul_le_mul_left V.card ambient)
  have empty := no_short_bank (score:=score) sv tv
    (disjoint_left.mpr (fun x sm tm=> by
      have a : score x<base := (mem_filter.mp sm).2
      have b : base+2≤score x := (mem_filter.mp tm).2
      omega))
    (fun x xm=>floor x (sv xm))
    (fun x xm=>le_of_not_gt (fun low=>(mem_sdiff.mp xm).2 (mem_filter.mpr ⟨(mem_sdiff.mp xm).1,low⟩)))
    (fun _ xm=>(mem_filter.mp xm).2) cap rows many
  intro x xm
  by_contra! low
  have failed : x∈S := mem_filter.mpr ⟨xm,low⟩
  rw [empty] at failed
  exact notMem_empty _ failed

attribute [aesop safe forward (immediate := [free,reg,hq,hr,time,pressure,many,radii,ambient,floor,shape,bonus])
  (rule_sets := [CHGraphFamilies])] paid_shells
#print axioms paid_shells

#print axioms supply
#print axioms remote_capacity
#print axioms no_short_bank
#print axioms full_rows
end LeanCH.BR.ConsecutiveShellBanks

