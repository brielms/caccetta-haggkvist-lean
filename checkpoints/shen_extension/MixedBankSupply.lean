import checkpoints.shen_extension.ExpandedBankRows
namespace LeanCH.BR.MixedBankSupply
open Finset BRq2 BRq3 BR45 BRsGen OneSpareGrowth ConsecutiveShellBanks ExpandedBankRows

/-- The common physical witnesses persist when the third layer has one
extra slot. In that case it is the retained degree on Y∪Z that pays the
fourth layer. -/
theorem marked_rows {D V q r k u} (free : QFree D V q) (hq : 5≤q) (root : u∈V)
    (reg : OutEq r D V) (hr : 2≤r) (time : k+3≤q) (pressure : r≤q+k+1)
    (ys : (N2 D V u).card+1=r) (zwidth : (N3 D V u).card+1=r ∨ (N3 D V u).card=r)
    (space : 2*r≤3*q+1) :
    let X := outN D V u
    let F := X.filter (fun w=>(outN D X w).card=1)
    2*q+2≤r+F.card ∧ ∀w∈F,2*r+1≤(ball D V w 2).card ∧ 3*r+1≤(ball D V w 3).card := by
  rcases zwidth with old|wide
  · exact full_rows free (by omega) root reg hr time pressure ys old
  have cut := free.mono_bound (show 4≤q by omega)
  have bound := outer_slots free hq root reg hr time pressure ys (by decide : 2≤3) (by decide)
    (show (N2 D V u).card+(N3 D V u).card≤q*3 by omega)
  let X := outN D V u
  have size : X.card=r := reg u root
  have xv : X⊆V := outN_subset
  have positive x (xm : x∈X) := internal_positive free (by omega) root reg ys xm
  have raw := LocalBallTransfer.light_supply (free.mono_set xv) (by omega)
    (card_pos.mp (by omega : 0<X.card)) positive (by omega)
  refine ⟨by simpa only [size] using raw,?_⟩
  intro w wm
  obtain ⟨wx,one⟩ := mem_filter.mp wm
  have head := sends_layer free (by omega) root reg ys wx one
  have a := full_row_credit (j:=2) free root wx (by decide) (by omega) positive head
  have b := full_row_credit (j:=3) free root wx (by decide) (by omega) positive head
  have row := card_B1 cut root
  rw [reg u root] at row
  have b2 := @card_B2 D V u
  have b3 := @card_B3 D V u
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
  simp only [Nat.reduceAdd] at a b
  omega

/-- Price one distinct high row per witness, with at most two units of
debt per low row. Missing directions pay skipped origins and the extra
label of each disjoint representative forces strict excess. -/
theorem no_deficit {V S T : Finset ℕ} {score : ℕ→ℕ} {base m d : ℕ}
    (sv : S⊆V) (tv : T⊆V) (apart : Disjoint S T)
    (low : ∀x∈S,base≤score x+2) (ordinary : ∀x∈V\S,base≤score x)
    (high : ∀x∈T,base+1≤score x) (cap : m+(∑x∈V,score x)≤V.card*base)
    (supply : ∃g,g≤S.card ∧ (S.Nonempty → 0<g) ∧ g*d≤T.card ∧ 2*(S.card-g)≤m)
    (extra : 3≤d) : S=∅ := by
  by_contra ne
  obtain ⟨g,gs,pos,cells,holes⟩ := supply
  have more := pos (nonempty_iff_ne_empty.mpr ne)
  have bound := (Nat.mul_le_mul_left g extra).trans cells
  have off : T⊆V\S := fun x xm=>mem_sdiff.mpr ⟨tv xm,fun h=>disjoint_left.mp apart h xm⟩
  have a := sum_le_sum low
  have b := RetainedRadiusLayers.add_layer (f:=fun _=>base) (g:=score) off ordinary high
  rw [sum_const_nat (fun _ _=>rfl),sum_add_distrib,sum_const_nat (fun _ _=>rfl)] at a
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset sv,Nat.mul_one] at b
  have := sum_sdiff sv (f:=score)
  have eq : (V.card-S.card)*base+S.card*base=V.card*base := by
    rw [←Nat.add_mul,Nat.sub_add_cancel (card_le_card sv)]
  omega

/-- Exclude all rows with score below the two-radius threshold when the
two supply profiles cover those rows. Shared witnesses retain the same
vertex in both directions of the missing pair. -/
theorem paid {D V q r k i j base} (f : QFree D V q) (hq : 5≤q) (reg : OutEq r D V)
    (hr : 2≤r) (time : k+3≤q) (pressure : r≤q+k+1) (space : 2*r≤3*q+1)
    (radii : i+j≤q) (size : V.card+1≤base) (many : 3≤2*q+2-r)
    (floor : ∀x∈V,base≤(ball D V x i).card+(ball D V x j).card+2)
    (shape : ∀x∈V,(ball D V x i).card+(ball D V x j).card<base →
      (N2 D V x).card+1=r ∧ ((N3 D V x).card+1=r ∨ (N3 D V x).card=r))
    (bonus : ∀x∈V,2*r+1≤(ball D V x 2).card → 3*r+1≤(ball D V x 3).card →
      base+1≤(ball D V x i).card+(ball D V x j).card) :
    ∀x∈V,base≤(ball D V x i).card+(ball D V x j).card := by
  classical
  let score := fun x=>(ball D V x i).card+(ball D V x j).card
  let S := V.filter (fun x=>score x<base)
  let T := V.filter (fun x=>base+1≤score x)
  let F := fun x=>(outN D V x).filter (fun w=>(outN D (outN D V x) w).card=1)
  have sv : S⊆V := filter_subset _ _
  have form x (sm : x∈S) := shape x (sv sm) (mem_filter.mp sm).2
  have marked x (sm : x∈S) := marked_rows f hq (sv sm) reg hr time pressure (form x sm).1 (form x sm).2 space
  have supply := SharedBankLedger.witness_budget (M:=DotClonePairCompletion.orderedIncomparable D V q) F
    (fun x (sm : x∈S)=>show 2*q+2-r≤(F x).card by have h := (marked x sm).1; change 2*q+2≤r+(F x).card at h; omega)
    (T:=T) (fun x sm w wm=>by
      obtain ⟨b,c⟩ := (marked x sm).2 w wm
      have wv := outN_subset (mem_filter.mp wm).1
      exact mem_filter.mpr ⟨wv,bonus w wv b c⟩) (by
      intro x xm y ym ne w hx hy
      have miss (a) (am : a∈S) (b) (bm : b∈S) (diff : a≠b) (aw : w∈F a) (bw : w∈F b) :=
        SharedLayerBarrier.shared_full_remote f (by omega) (sv am) (sv bm) diff reg
          (form a am).1 (form b bm).1 (mem_filter.mp aw).1 (mem_filter.mp bw).1
          (sends_layer f (by omega) (sv am) reg (form a am).1 (mem_filter.mp aw).1 (mem_filter.mp aw).2)
          (sends_layer f (by omega) (sv bm) reg (form b bm).1 (mem_filter.mp bw).1 (mem_filter.mp bw).2)
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨sv xm,sv ym,ne⟩,miss x xm y ym ne hx hy,miss y ym x xm ne.symm hy hx⟩)
  have empty := no_deficit (S:=S) (T:=T) (score:=score) sv (filter_subset _ _) (by
    apply disjoint_left.mpr
    intro x a b
    have lo : score x<base := (mem_filter.mp a).2
    have hi : base+1≤score x := (mem_filter.mp b).2
    omega) (fun x xm=>floor x (sv xm)) (by
      intro x xm
      exact le_of_not_gt (fun low=>(mem_sdiff.mp xm).2 (mem_filter.mpr ⟨(mem_sdiff.mp xm).1,low⟩)))
    (fun _ xm=>(mem_filter.mp xm).2) ((remote_capacity f radii).trans (Nat.mul_le_mul_left _ size)) supply many
  intro x xm
  by_contra! fail
  have hit : x∈S := mem_filter.mpr ⟨xm,fail⟩
  rw [empty] at hit
  exact notMem_empty _ hit

attribute [aesop safe forward (immediate := [free,hq,root,reg,hr,time,pressure,ys,zwidth,space])
  (rule_sets := [CHGraphFamilies])] marked_rows
attribute [aesop safe forward (immediate := [sv,tv,apart,low,ordinary,high,cap,supply,extra])
  (rule_sets := [CHGraphFamilies])] no_deficit
attribute [aesop safe forward (immediate := [f,hq,reg,hr,time,pressure,space,radii,size,many,floor,shape,bonus])
  (rule_sets := [CHGraphFamilies])] paid
#print axioms marked_rows
#print axioms no_deficit
#print axioms paid
end LeanCH.BR.MixedBankSupply
