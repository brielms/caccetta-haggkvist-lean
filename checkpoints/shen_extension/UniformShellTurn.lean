import checkpoints.shen_extension.CommonBankPath
import checkpoints.shen_extension.UniformSinkExclusion
namespace LeanCH.BR.ThinRowTurn
open Finset BRq2 BRq3 BR45 BRsGen

/-- Reapply the forced turn on its actual successor. The vertex serving
Z and its entire labelled head bank are kept throughout the walk. -/
theorem propagate {D V X Y Z q r c y} (free : QFree D V q) (hq : 5≤q)
    (xv : X⊆V) (yv : Y⊆V) (zv : Z⊆V) (xy : Disjoint X Y) (sep : Disjoint (X∪Y) Z)
    (reg : OutEq r D V) (low : 2≤r) (width : r≤q+3) (dz : Z.card+1=r)
    (rows : ∀v∈X,outN D V v⊆X∪Y) (inside : ∀v∈X,(outN D X v).Nonempty)
    (cx : c∈X) (head : y∈outN D Y c) (big : Z⊆outN D V y)
    (size : ∀v∈X,(ball D V v 2).card≤2*r+1) : 3*r+1≤(ball D V c 3).card := by
  classical
  let B := outN D Y c
  let State := {v : ℕ // v∈X ∧ outN D Y v=B}
  have step (v : State) : ∃a : State,D v.val a.val=true := by
    have current : y∈outN D Y v.val := v.property.2.symm ▸ head
    obtain ⟨a,ax,one,same,_⟩ := forced_turn free (by omega) xv yv zv xy sep reg rows inside
      v.property.1 current big dz (size v.val v.property.1)
    exact ⟨⟨a,ax,same.trans v.property.2⟩,(mem_outN.mp (one.symm ▸ mem_singleton_self a)).2⟩
  let next := fun (v : State)=>Classical.choose (step v)
  let start : State := ⟨c,cx,rfl⟩
  let orbit := fun i=>(next^[i]) start
  let f := fun i=>(orbit i).val
  have member i : f i∈X := (orbit i).property.1
  have preserved i : outN D Y (f i)=B := (orbit i).property.2
  have edge i : D (f i) (f (i+1))=true := by
    change D (orbit i).val (((next^[i+1]) start).val)=true
    rw [Function.iterate_succ_apply']
    exact Classical.choose_spec (step (orbit i))
  obtain ⟨_,_,_,_,db⟩ := forced_turn free (by omega) xv yv zv xy sep reg rows inside
    cx head big dz (size c cx)
  have by' : B⊆Y := outN_subset
  have common i : B⊆outN D V (f i) := (preserved i) ▸ outN_mono yv (f i)
  have reach i : Z⊆ball D V (f i) 2 := fun a am=>ball_step
    (ball_of_adj (yv (outN_subset head)) (mem_outN.mp (common i head)).2)
    (zv am) (mem_outN.mp (big am)).2
  have xbz : Disjoint X (B∪Z) := by
    apply disjoint_left.mpr
    intro a ax ab
    rcases mem_union.mp ab with ab|az
    · exact disjoint_left.mp xy ax (by' ab)
    · exact disjoint_left.mp sep (mem_union_left _ ax) az
  exact third_excess free hq xv (by'.trans yv) zv xbz
    (sep.mono_left (by'.trans subset_union_right)) db dz low width (fun a am=>(reg a am).ge)
    f member edge common reach (fun i=>size _ (member i))

/-- In a punctured ball with all first rows at full degree, either a
second row fills the third layer, or the rank-two density rule closes
the carrier. -/
theorem seed {D V q r u} (free : QFree D V q) (hq : 5≤q) (root : u∈V) (reg : OutEq r D V)
    (hr : 4≤r) (room : r+2≤2*q) (cost : (2*r)*(2*r+1)≤r*(2*r+6)+r*12)
    (dy : (N2 D V u).card=r) (dz : (N3 D V u).card+1=r) :
    ∃c∈outN D V u,∃y∈outN D (N2 D V u) c,N3 D V u⊆outN D V y := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have full v (vm : v∈X) : r≤(outN D (X∪Y) v).card := by
    rw [←outN_X_eq (free.mono_bound (by omega : 4≤q)) root vm,reg v (xv vm)]
  have dx : X.card=r := reg u root
  have sep : Disjoint X Y := disjXY
  have dxy := card_union_of_disjoint sep
  have rest : (X∪Y)\X=Y := by ext a; simp only [mem_sdiff,mem_union]; constructor
                                    <;> grind [disjoint_left.mp sep]
  change Y.card=r at dy
  have light : ∃y∈Y,(outN D (X∪Y) y).card≤1 := by
    by_contra! high
    apply FullRowEscape.dense_fragment (free.mono_set (union_subset xv yv)) hq
      (fun v vm=> (mem_union.mp vm).elim (fun vx=>(show 2≤r by omega).trans (full v vx)) (high v))
      subset_union_left full hr room
    · rw [rest]
      exact card_pos.mp (by omega)
    · rw [rest]; omega
    · rw [dxy,dy,dx]
      simpa only [←two_mul,show 2*r-r=r by omega] using cost
  obtain ⟨y,ym,few⟩ := light
  obtain ⟨c,cm,arc⟩ := parY root ym
  refine ⟨c,cm,y,mem_outN.mpr ⟨ym,arc⟩,?_⟩
  have sub : outN D V y⊆outN D (X∪Y) y∪outN D Z y := by
    intro a am
    have edge := (mem_outN.mp am).2
    rcases headY (free.mono_bound (by omega : 4≤q)) root ym (outN_subset am) edge with old|new'
    · exact mem_union_left _ (mem_outN.mpr ⟨old,edge⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨new',edge⟩)
  have cap := (card_le_card sub).trans (card_union_le _ _)
  rw [reg y (yv ym)] at cap
  change Z.card+1=r at dz
  have whole : outN D Z y=Z := eq_of_subset_of_card_le outN_subset (by omega)
  change Z⊆outN D V y
  exact whole ▸ (outN_mono (show Z⊆V from fun _ h=>N3_subV h) y : outN D Z y⊆outN D V y)

attribute [aesop safe forward (immediate := [free,hq,xv,yv,zv,xy,sep,reg,low,width,dz,rows,inside,cx,head,big,size]) (rule_sets := [CHGraphFamilies])] propagate
attribute [aesop safe forward (immediate := [free,hq,root,reg,hr,room,cost,dy,dz]) (rule_sets := [CHGraphFamilies])] seed
#print axioms propagate
#print axioms seed
end LeanCH.BR.ThinRowTurn
