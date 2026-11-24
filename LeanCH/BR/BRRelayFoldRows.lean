import LeanCH.BR.BRRelayFoldSafety

namespace LeanCH.BR.WeightedSD.RelayFold
open Finset BRq2 BRq3 BR45 BRsub

noncomputable def boost (t x : ℕ) : ℚ := 1 + if x=t then 1 else 0
noncomputable def losses (D : CH.Digraph) (V : Finset ℕ) (u h t x : ℕ) :=
  (outN D V x) ∩ insert u (X1 D V u h t)

theorem mass_boost (S : Finset ℕ) (t : ℕ) :
    mass S (boost t)=(S.card:ℚ)+(if t∈S then 1 else 0) := by
  classical
  simp [mass,boost,sum_add_distrib]

theorem row_boost (q : ℕ) (D : CH.Digraph) (S : Finset ℕ) (t x : ℕ) :
    row q D S (boost t) x=1+(if x=t then 1 else 0)+
      q*((outN D S x).card:ℚ)+q*(if t∈outN D S x then 1 else 0) := by
  rw [row,outW_eq_mass,mass_boost]
  simp only [boost]
  ring

namespace Base
variable {D : CH.Digraph} {V : Finset ℕ} {u h t : ℕ} (B : Base D V u h t)
include B
variable {K : Finset (ℕ×ℕ)} {Q : ℕ→Finset ℕ}

theorem edge_X0 (hK : ValidCuts D V u h t K) {x y : ℕ} (hx : x∈X0 D V u h t) :
    graph D V u h t K Q x y=true ↔ D x y=true ∨ y=u := by
  have f := B.X_facts (X0_X hx)
  have nx1 : x∉X1 D V u h t := fun h1=>disjoint_left.mp X_disjoint hx h1
  have nxR : x∉R D V u h t := fun hr=>(B.R_facts hr).2.2.2.2.1 (X0_X hx)
  have nk : (x,y)∉K := fun hk=>nx1 (hK x y hk).1
  simp [graph_edge,Old,New,hx,f.2.1,nx1,nxR,nk]

theorem edge_X1 {x y : ℕ} (hx : x∈X1 D V u h t) :
    graph D V u h t K Q x y=true ↔ (D x y=true ∧ (x,y)∉K) ∨ y=t := by
  have f := B.X_facts (X1_X hx)
  have nx0 : x∉X0 D V u h t := fun h0=>disjoint_left.mp X_disjoint h0 hx
  have nxR : x∉R D V u h t := fun hr=>(B.R_facts hr).2.2.2.2.1 (X1_X hx)
  simp [graph_edge,Old,New,hx,f.2.1,nx0,nxR]

theorem edge_u (hK : ValidCuts D V u h t K) (y : ℕ) :
    graph D V u h t K Q u y=true ↔ (D u y=true ∧ y∉C D V u h t) ∨ y=t := by
  have nx : u∉X D V h t := fun hx=>B.miss_h (mem_X.mp hx).2.1
  have nx0 : u∉X0 D V u h t := fun hx=>nx (X0_X hx)
  have nx1 : u∉X1 D V u h t := fun hx=>nx (X1_X hx)
  have nxR : u∉R D V u h t := fun hr=>(B.R_facts hr).2.1 rfl
  have nk : (u,y)∉K := fun hk=>nx1 (hK u y hk).1
  simp [graph_edge,Old,New,nx0,nx1,nxR,nk]

theorem edge_R (hK : ValidCuts D V u h t K) {x y : ℕ} (hx : x∈R D V u h t) :
    graph D V u h t K Q x y=true ↔
      (D x y=true ∧ y≠u ∧ y∉X1 D V u h t) ∨ y∈Q x := by
  have f := B.R_facts hx
  have nx0 : x∉X0 D V u h t := fun h0=>f.2.2.2.2.1 (X0_X h0)
  have nx1 : x∉X1 D V u h t := fun h1=>f.2.2.2.2.1 (X1_X h1)
  have nk : (x,y)∉K := fun hk=>nx1 (hK x y hk).1
  simp [graph_edge,Old,New,hx,f.2.1,nx0,nx1,nk]

omit B in
theorem edge_other (hK : ValidCuts D V u h t K) {x y : ℕ}
    (hxu : x≠u) (hx0 : x∉X0 D V u h t) (hx1 : x∉X1 D V u h t)
    (hxR : x∉R D V u h t) : graph D V u h t K Q x y=true ↔ D x y=true := by
  have nk : (x,y)∉K := fun hk=>hx1 (hK x y hk).1
  simp [graph_edge,Old,New,hxu,hx0,hx1,hxR,nk]

theorem heads_X0 (hK : ValidCuts D V u h t K) {x : ℕ} (hx : x∈X0 D V u h t) :
    outN (graph D V u h t K Q) (V.erase h) x=insert u ((outN D V x).erase h) := by
  classical
  ext y
  simp only [mem_outN,mem_erase,B.edge_X0 hK hx,mem_insert]
  have hu := B.umem
  have huh := B.uh
  aesop

theorem heads_X1 (hK : ValidCuts D V u h t K) {x : ℕ} (hx : x∈X1 D V u h t) :
    outN (graph D V u h t K Q) (V.erase h) x=
      insert t (outN D V x \ insert h (cutHeads V K x)) := by
  classical
  ext y
  simp only [mem_outN,mem_erase,B.edge_X1 hx,mem_insert,mem_sdiff,cutHeads,mem_filter]
  have ht := B.tmem
  have hth := B.ht.symm
  aesop

theorem heads_u (hK : ValidCuts D V u h t K) :
    outN (graph D V u h t K Q) (V.erase h) u=insert t (outN D V u \ C D V u h t) := by
  classical
  ext y
  simp only [mem_outN,mem_erase,B.edge_u hK,mem_insert,mem_sdiff]
  have ht := B.tmem
  have hth := B.ht.symm
  have nh := B.miss_h
  aesop

theorem heads_R (hK : ValidCuts D V u h t K) (hQ : Selected D V u h t K Q)
    {x : ℕ} (hx : x∈R D V u h t) :
    outN (graph D V u h t K Q) (V.erase h) x=
      (outN D V x \ losses D V u h t x) ∪ Q x := by
  classical
  have nh := (B.R_facts hx).2.2.2.2.2.2.1
  have qs : ∀y∈Q x,y∈V ∧ y≠h := fun y hy=>
    ⟨(mem_W.mp (mem_eligible.mp (hQ x hx hy)).1).1,
      (mem_W.mp (mem_eligible.mp (hQ x hx hy)).1).2.1⟩
  ext y
  simp only [mem_outN,mem_erase,B.edge_R hK hx,mem_union,mem_sdiff,losses,mem_inter,mem_insert]
  specialize qs y
  aesop

omit B in
theorem heads_other (hK : ValidCuts D V u h t K) {x : ℕ}
    (hxu : x≠u) (hx0 : x∉X0 D V u h t) (hx1 : x∉X1 D V u h t)
    (hxR : x∉R D V u h t) :
    outN (graph D V u h t K Q) (V.erase h) x=(outN D V x).erase h := by
  ext y
  simp only [mem_outN,mem_erase,edge_other hK hxu hx0 hx1 hxR]
  tauto

theorem losses_card (x : ℕ) :
    (losses D V u h t x).card=(if D x u=true then 1 else 0)+
      ((outN D V x)∩X1 D V u h t).card := by
  classical
  have nu : u∉(outN D V x)∩X1 D V u h t := by
    intro hu
    exact B.miss_h (mem_X1.mp (mem_inter.mp hu).2).2.1
  unfold losses
  by_cases hu : D x u=true
  · have hm : u∈outN D V x := mem_outN.mpr ⟨B.umem,hu⟩
    rw [inter_insert_of_mem hm,card_insert_of_notMem nu]
    simp [hu,add_comm]
  · have hm : u∉outN D V x := fun hm=>hu (mem_outN.mp hm).2
    rw [inter_insert_of_notMem hm]
    simp [hu]

theorem K_heads (hK : ValidCuts D V u h t K) (x : ℕ) :
    cutHeads V K x⊆outN D V x ∧ h∉cutHeads V K x := by
  classical
  constructor
  · intro y hy
    obtain ⟨hyV,hxy⟩ := mem_filter.mp hy
    exact mem_outN.mpr ⟨hyV,(hK x y hxy).2.2⟩
  · intro hh
    exact (B.R_facts (hK x h (mem_filter.mp hh).2).2.1).2.2.1 rfl

theorem row_X0 (hK : ValidCuts D V u h t K) (q : ℕ) {x : ℕ}
    (hx : x∈X0 D V u h t) :
    row q (graph D V u h t K Q) (V.erase h) (boost t) x=
      row q D V (fun _=>1) x := by
  classical
  have f := B.X_facts (X0_X hx)
  have hh : h∈outN D V x := mem_outN.mpr ⟨B.hmem,f.2.2.2.2.1⟩
  have nu : u∉(outN D V x).erase h := fun hu=>
    (mem_X0.mp hx).2.2.2 (mem_outN.mp (mem_erase.mp hu).2).2
  rw [row_boost,B.heads_X0 hK hx,card_insert_of_notMem nu]
  have hc := card_erase_add_one hh
  have ht : t∉insert u ((outN D V x).erase h) := by
    simp [mem_insert,mem_erase,mem_outN,B.ut.symm,f.2.2.2.2.2.1]
  simp only [ht,ite_false,f.2.2.2.1,Nat.cast_add,Nat.cast_one,row,outW_unit]
  have he : ((outN D V x).erase h).card+1=(outN D V x).card := hc
  have heq := congrArg (fun n:ℕ=>(n:ℚ)) he
  push_cast at heq
  nlinarith

theorem row_X1 (hK : ValidCuts D V u h t K) (q : ℕ) {x : ℕ}
    (hx : x∈X1 D V u h t) :
    row q (graph D V u h t K Q) (V.erase h) (boost t) x+
      q*((cutHeads V K x).card:ℚ)=row q D V (fun _=>1) x+q := by
  classical
  have f := B.X_facts (X1_X hx)
  have hh : h∈outN D V x := mem_outN.mpr ⟨B.hmem,f.2.2.2.2.1⟩
  have hs : insert h (cutHeads V K x)⊆outN D V x := insert_subset hh (B.K_heads hK x).1
  have nt : t∉outN D V x := fun ht=>f.2.2.2.2.2.1 (mem_outN.mp ht).2
  have nt' : t∉outN D V x \ insert h (cutHeads V K x) := fun ht=>nt (mem_sdiff.mp ht).1
  have hc := card_sdiff_add_card_eq_card hs
  rw [card_insert_of_notMem (B.K_heads hK x).2] at hc
  have he := congrArg (fun n:ℕ=>(n:ℚ)) hc
  push_cast at he
  rw [row_boost,B.heads_X1 hK hx,card_insert_of_notMem nt']
  simp only [mem_insert_self,ite_true,f.2.2.2.1,ite_false,Nat.cast_add,Nat.cast_one,row,outW_unit]
  nlinarith

theorem row_u (hK : ValidCuts D V u h t K) (q : ℕ) :
    row q (graph D V u h t K Q) (V.erase h) (boost t) u+
      q*((C D V u h t).card:ℚ)=row q D V (fun _=>1) u+2*q := by
  classical
  have hs : C D V u h t⊆outN D V u := fun y hy=>
    mem_outN.mpr ⟨(mem_C.mp hy).1,(mem_C.mp hy).2.1⟩
  have nt : t∉outN D V u \ C D V u h t := fun ht=>B.miss_t (mem_outN.mp (mem_sdiff.mp ht).1).2
  have hc := congrArg (fun n:ℕ=>(n:ℚ)) (card_sdiff_add_card_eq_card hs)
  push_cast at hc
  rw [row_boost,B.heads_u hK,card_insert_of_notMem nt]
  simp only [mem_insert_self,ite_true,B.ut,ite_false,Nat.cast_add,Nat.cast_one,row,outW_unit]
  nlinarith

theorem row_R (hK : ValidCuts D V u h t K) (hQ : Selected D V u h t K Q)
    (q : ℕ) {x : ℕ} (hx : x∈R D V u h t) :
    row q (graph D V u h t K Q) (V.erase h) (boost t) x+
      q*((losses D V u h t x).card:ℚ)=row q D V (fun _=>1) x+q*((Q x).card:ℚ) := by
  classical
  have f := B.R_facts hx
  have hs : losses D V u h t x⊆outN D V x := inter_subset_left
  have hd : Disjoint (outN D V x \ losses D V u h t x) (Q x) := by
    apply disjoint_left.mpr
    intro z hz hzQ
    exact (mem_eligible.mp (hQ x hx hzQ)).2.1 (mem_outN.mp (mem_sdiff.mp hz).1).2
  have nt : t∉(outN D V x \ losses D V u h t x)∪Q x := by
    intro ht
    rcases mem_union.mp ht with ht|ht
    · exact f.2.2.2.2.2.2.2.1 (mem_outN.mp (mem_sdiff.mp ht).1).2
    · exact (mem_W.mp (mem_eligible.mp (hQ x hx ht)).1).2.2.1 rfl
  have hc := congrArg (fun n:ℕ=>(n:ℚ)) (card_sdiff_add_card_eq_card hs)
  push_cast at hc
  rw [row_boost,B.heads_R hK hQ hx,card_union_of_disjoint hd]
  simp only [nt,ite_false,f.2.2.2.1,Nat.cast_add,row,outW_unit]
  nlinarith

theorem row_other (hK : ValidCuts D V u h t K) (q : ℕ) {x : ℕ}
    (hxu : x≠u) (hx0 : x∉X0 D V u h t) (hx1 : x∉X1 D V u h t)
    (hxR : x∉R D V u h t) :
    row q (graph D V u h t K Q) (V.erase h) (boost t) x+
      q*(if D x h=true then 1 else 0)=row q D V (fun _=>1) x+
        (if x=t then 1 else 0)+q*(if D x t=true then 1 else 0) := by
  classical
  rw [row_boost,heads_other hK hxu hx0 hx1 hxR]
  have hte : t∈(outN D V x).erase h ↔ D x t=true := by
    simp [mem_outN,B.tmem,B.ht.symm]
  rw [if_congr hte rfl rfl]
  by_cases hh : D x h=true
  · have hm : h∈outN D V x := mem_outN.mpr ⟨B.hmem,hh⟩
    have hc := congrArg (fun n:ℕ=>(n:ℚ)) (card_erase_add_one hm)
    push_cast at hc
    simp only [hh,ite_true,row,outW_unit]
    nlinarith
  · have hm : h∉outN D V x := fun hm=>hh (mem_outN.mp hm).2
    rw [erase_eq_of_notMem hm]
    simp [hh,row,outW_unit]
    ring

end Base
end LeanCH.BR.WeightedSD.RelayFold
