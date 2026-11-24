import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Order33_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Charges_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5BankPacking_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen
open scoped BigOperators
private theorem sum_mixed {D : CH.Digraph} {U : Finset ℕ}
    (hf : QFree D U 5) :
    (∑ v ∈ U, ((ball D U v 2).card+(ball D U v 3).card))≤U.card*(U.card+1) := by
  classical
  have localB (v) (hv : v∈U) : (ball D U v 2).card+(reverseBall D U v 3).card≤U.card+1 := by
    let F := ball D U v 2
    let I := reverseBall D U v 3
    have hI : I⊆(U \ F) ∪ {v} := reverseBall_subset_complement hf (by decide : 2+3≤5)
    have hmeet : F∩I={v} := by
      ext y
      constructor
      · intro m
        obtain ⟨f,g⟩ := mem_inter.mp m
        rcases mem_union.mp (hI g) with h | h
        · exact ((mem_sdiff.mp h).2 f).elim
        · exact h
      · intro m
        obtain rfl := mem_singleton.mp m
        exact mem_inter.mpr ⟨self_mem_ball hv,mem_filter.mpr ⟨hv,self_mem_ball hv⟩⟩
    have hsub : F∪I ⊆ U := union_subset ball_subset (filter_subset _ _)
    have h2 := card_union_add_card_inter F I
    rw [hmeet,card_singleton] at h2
    have h1 := card_le_card hsub
    change F.card+I.card≤U.card+1
    omega
  have agg := sum_le_sum localB
  rw [sum_add_distrib,sum_reverseBall_eq_sum_ball,Finset.sum_const_nat (fun _ _ => rfl)] at agg
  rw [sum_add_distrib]
  exact agg


private theorem walk_host {D : CH.Digraph} {X V : Finset ℕ} {v k : ℕ}
    (h : X⊆V) : ball D X v k⊆ball D V v k := by
  intro x hx
  obtain ⟨xX,i,ik,w⟩ := mem_ball.mp hx
  exact mem_ball.mpr ⟨h xX,i,ik,w.mono h⟩

private theorem blocked_equal_profile {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hne : V.Nonempty)
    (f2 : ∀ v∈V, (ball D V v 2).card=14)
    (f3 : ∀ v∈V, (ball D V v 3).card=21) : False := by
  obtain ⟨u,hu⟩ := hne
  let A := (ball D V u 1).erase u
  let B := SecondBank D V u
  let T := ball D V u 3 \ ball D V u 2
  obtain ⟨_,b6,M,P,mA,_,m1,pM,p4,pB,_⟩ := six_bank_first_layer hf ho hu (f2 u hu)
  change B.card=6 at b6
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have tv : T⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have t7 : T.card=7 := by
    have sp := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    change T.card+(ball D V u 2).card=(ball D V u 3).card at sp
    rw [f2 u hu,f3 u hu] at sp
    omega
  obtain ⟨c,hc⟩ := card_pos.mp (by omega : 0<P.card)
  let J := ball D M c 2
  have ja : J⊆A := ball_subset.trans mA
  have je : J⊆ball D V c 2 := walk_host (mA.trans av)
  have jb : 3≤J.card :=
    ball_one_growth (hf.mono_set (mA.trans av)) (fun v hv => (m1 v hv).ge) (pM hc) 2 (by decide)
  have br : B⊆ball D V c 1 := fun b hb =>
    mem_ball.mpr ⟨bv hb,1,by decide,.step (bv hb) (pB c hc b hb) (.refl b)⟩
  have tr : T⊆ball D V c 2 := by
    intro t ht
    have ⟨_,k,k3,w⟩ := mem_ball.mp (mem_sdiff.mp ht).1
    have ek : k=3 := by
      by_contra ne
      exact (mem_sdiff.mp ht).2 (mem_ball.mpr ⟨tv ht,k,by omega,w⟩)
    subst k
    obtain ⟨b,p,_,e⟩ := w.unsnoc
    have bv' : b∈V := (p.end_mem_or).elim (fun h => h.symm ▸ hu) id
    have bb : b∈B := by
      refine mem_sdiff.mpr ⟨mem_ball.mpr ⟨bv',2,by decide,p⟩,?_⟩
      intro h
      exact (mem_sdiff.mp ht).2 (ball_step h (tv ht) e)
    exact ball_step (br bb) (tv ht) e
  have db : Disjoint J B := disjoint_left.mpr
    (fun _ j b => (mem_sdiff.mp b).2 (mem_of_mem_erase (ja j)))
  have dt : Disjoint (J∪B) T := disjoint_left.mpr (by
    intro x h t
    rcases mem_union.mp h with j|b
    · exact (mem_sdiff.mp t).2 (ball_mono_radius (by decide : 1≤2) (mem_of_mem_erase (ja j)))
    · exact (mem_sdiff.mp t).2 (mem_sdiff.mp b).1)
  have ct := card_le_card (union_subset
    (union_subset je (br.trans (ball_mono_radius (by decide : 1≤2)))) tr)
  rw [card_union_of_disjoint dt,card_union_of_disjoint db,b6,t7,f2 c (av (mA (pM hc)))] at ct
  omega

/-- The entire order-34 cutoff-five case is excluded without imposing
in-regularity. Each carrier and each capacity column is on the thinned host. -/
theorem five_free_ge35 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hm : ∀ v∈V,7≤(outN D V v).card) (hne : V.Nonempty) :
    35≤V.card := by
  classical
  by_contra! small
  have n34 : V.card=34 := by have h := five_free_ge34 hf hm hne; omega
  obtain ⟨G,sub,ho⟩ := exists_outEq hm
  have free := qfree_sub sub hf
  have deg (v) (hv : v∈V) : 7≤(outN G V v).card := (ho v hv).ge
  let L := V.filter (fun v => (ball G V v 3).card=20)
  let bank := SecondBank G V
  let K := L.image bank
  have lv : L⊆V := filter_subset _ _
  have lt (v) (hv : v∈L) : (ball G V v 3).card=20 := (mem_filter.mp hv).2
  have bV (u : ℕ) : bank u⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have ex (B : Finset ℕ) (h : B∈K) : ∃ u∈L, bank u=B := mem_image.mp h
  choose r rl rb using ex
  have br (B : Finset ℕ) (h : B∈K) : B⊆V := rb B h ▸ bV (r B h)
  have spill (B : Finset ℕ) (h : B∈K) :
      ∃ T, B.card=6 ∧ OutEq 1 G B ∧ (∀ b∈B, outN G V b⊆B∪T) ∧
        (∀ b∈B, ∀ t∈T, G b t=true) := by
    obtain ⟨bc,_,out,keep,all,_⟩ :=
      tight_spill_geometry free ho (lv (rl B h)) (lt _ (rl B h))
    change (bank (r B h)).card=6 at bc
    rw [rb B h] at bc
    refine ⟨ball G V (r B h) 3 \ ball G V (r B h) 2,bc,?_,?_,?_⟩
    · change OutEq 1 G (bank (r B h)) at out
      rwa [rb B h] at out
    · change (∀ b∈bank (r B h), outN G V b⊆bank (r B h) ∪ _) at keep
      rwa [rb B h] at keep
    · change (∀ b∈bank (r B h), ∀ t∈_, G b t=true) at all
      rwa [rb B h] at all
  have bdis : (↑K : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro B hB C hC ne
    have hb : B∈K := hB
    have hc : C∈K := hC
    obtain ⟨T,bc,be,bk,bt⟩ := spill B hb
    obtain ⟨U,cc,ce,ck,ct⟩ := spill C hc
    exact (spill_banks_disjoint_or_equal free (br B hb) (br C hc) bc cc be ce bk ck bt ct).resolve_right ne
  let good := fun (k : ℕ) (v : ℕ) =>
    15≤(ball G V v 2).card ∧ k≤(ball G V v 3).card
  have ck (B : Finset ℕ) (h : B∈K) :
      (∀ b∈B, good 21 b) ∧ ∃ P : Finset ℕ, P⊆V ∧ Disjoint B P ∧ P.card=4 ∧
        (∀ c∈P, ∀ b∈B, G c b=true) ∧ (∀ c∈P, good 22 c) := by
    have hh := tight_bank_charges free ho (lv (rl B h)) (lt _ (rl B h))
    change (∀ b∈bank (r B h), good 21 b) ∧
      (∃ P : Finset ℕ, P⊆V ∧ Disjoint (bank (r B h)) P ∧ P.card=4 ∧
        (∀ c∈P, ∀ b∈bank (r B h), G c b=true) ∧ (∀ c∈P, good 22 c)) at hh
    rwa [rb B h] at hh
  let P (B : Finset ℕ) : Finset ℕ := if h : B∈K then Classical.choose (ck B h).2 else ∅
  have pSpec (B : Finset ℕ) (h : B∈K) :
      P B⊆V ∧ Disjoint B (P B) ∧ (P B).card=4 ∧
        (∀ c∈P B, ∀ b∈B, G c b=true) ∧ ∀ c∈P B, good 22 c := by
    simpa only [P,dite_eq_left h] using Classical.choose_spec (ck B h).2
  have pdis : (↑K : Set (Finset ℕ)).PairwiseDisjoint P := by
    intro B hB C hC ne
    have hb : B∈K := hB
    have hc : C∈K := hC
    obtain ⟨_,bc,_,_,_⟩ := spill B hb
    obtain ⟨_,cc,_,_,_⟩ := spill C hc
    have bd := bdis hB hC ne
    change Disjoint B C at bd
    refine disjoint_left.mpr ?_
    intro x xp xq
    have arcs : B∪C⊆outN G V x := by
      intro a ha
      rcases mem_union.mp ha with h|h
      · exact mem_outN.mpr ⟨br B hb h,(pSpec B hb).2.2.2.1 x xp a h⟩
      · exact mem_outN.mpr ⟨br C hc h,(pSpec C hc).2.2.2.1 x xq a h⟩
    have no := card_le_card arcs
    rw [card_union_of_disjoint bd,bc,cc,ho x ((pSpec B hb).1 xp)] at no
    omega
  let U := K.biUnion id
  let E := K.biUnion P
  have cu : U.card=6*K.card := by
    rw [show U=K.biUnion id from rfl,card_biUnion bdis]
    calc
      _ = ∑ B∈K, (6 : ℕ) := sum_congr rfl (fun B hb => (spill B hb).choose_spec.1)
      _ = 6*K.card := by rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm]
  have ce : E.card=4*K.card := by
    rw [show E=K.biUnion P from rfl,card_biUnion pdis]
    calc
      _ = ∑ B∈K, (4 : ℕ) := sum_congr rfl (fun B hb => (pSpec B hb).2.2.1)
      _ = 4*K.card := by rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm]
  have uv : U⊆V := biUnion_subset.mpr br
  have ev : E⊆V := biUnion_subset.mpr (fun B h => (pSpec B h).1)
  have ug (v : ℕ) (h : v∈U) : good 21 v := by
    obtain ⟨B,hb,mem⟩ := mem_biUnion.mp h
    exact (ck B hb).1 v mem
  have eg (v : ℕ) (h : v∈E) : good 22 v := by
    obtain ⟨B,hb,mem⟩ := mem_biUnion.mp h
    exact (pSpec B hb).2.2.2.2 v mem
  let F (B : Finset ℕ) := L.filter (fun x => bank x=B)
  have group (B : Finset ℕ) (hb : B∈K) : (F B).card≤8 := by
    obtain ⟨_,bc,one,_,_⟩ := spill B hb
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<B.card)
    let Ba := ball G B a 2
    have ba3 : 3≤Ba.card :=
      ball_one_growth (free.mono_set (br B hb)) (fun v hv => (one v hv).ge) ha 2 (by decide)
    -- Choose three predecessors using the reverse twice-ball total.
    have existsCol : ∃ b∈B, 3≤(reverseBall G B b 2).card := by
      by_contra! no
      have lb : B.card*3≤∑ a∈B,(ball G B a 2).card := by
        rw [←Finset.sum_const_nat (fun _ _ => rfl)]
        exact sum_le_sum (fun a ha =>
          ball_one_growth (free.mono_set (br B hb)) (fun v hv => (one v hv).ge) ha 2 (by decide))
      have ub : (∑ a∈B,(reverseBall G B a 2).card)≤B.card*2 := by
        rw [←Finset.sum_const_nat (fun _ _ => rfl)]
        exact sum_le_sum (fun v hv => Nat.le_of_lt_succ (no v hv))
      rw [sum_reverseBall_eq_sum_ball,bc] at ub
      rw [bc] at lb
      omega
    obtain ⟨b,bB,cb3⟩ := existsCol
    obtain ⟨I,iSub,i3⟩ := exists_subset_card_eq cb3
    have iB : I⊆B := iSub.trans (filter_subset _ _)
    have iCol : I⊆reverseBall G V b 2 := fun a ha => by
      obtain ⟨aB,reach⟩ := mem_filter.mp (iSub ha)
      exact mem_filter.mpr ⟨br B hb aB,walk_host (br B hb) reach⟩
    have pCol : P B⊆reverseBall G V b 2 := fun c hc =>
      mem_filter.mpr ⟨(pSpec B hb).1 hc,mem_ball.mpr
        ⟨br B hb bB,1,by decide,.step (br B hb bB) ((pSpec B hb).2.2.2.1 c hc b bB) (.refl b)⟩⟩
    have fCol : F B⊆reverseBall G V b 2 := fun c hc => by
      obtain ⟨cl,eq⟩ := mem_filter.mp hc
      have m : b∈bank c := eq.symm ▸ bB
      exact mem_filter.mpr ⟨lv cl,(mem_sdiff.mp m).1⟩
    have dis : Disjoint (I∪P B) (F B) := disjoint_left.mpr (by
      intro x hx hy
      have h := lt x (mem_filter.mp hy).1
      rcases mem_union.mp hx with hI|hP
      · have hgood := ((ck B hb).1 x (iB hI)).2
        omega
      · have hgood := ((pSpec B hb).2.2.2.2 x hP).2
        omega)
    have cap := bank_group_bound free deg n34 (br B hb bB) i3 (pSpec B hb).2.2.1
      ((pSpec B hb).2.1.mono_left iB) dis iCol pCol fCol
    omega
  have cover : L⊆K.biUnion F := by
    intro v hv
    exact mem_biUnion.mpr ⟨bank v,mem_image.mpr ⟨v,hv,rfl⟩,mem_filter.mpr ⟨hv,rfl⟩⟩
  have boundL : L.card≤8*K.card := by
    calc
      _ ≤ (K.biUnion F).card := card_le_card cover
      _ ≤ ∑ B∈K, (F B).card := card_biUnion_le
      _ ≤ ∑ B∈K, (8 : ℕ) := sum_le_sum group
      _ = 8*K.card := by rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm]
  let score (v : ℕ) := (ball G V v 2).card+(ball G V v 3).card
  have upper : (∑ v∈V,score v)≤35*V.card := by
    have sq := sum_mixed free
    change (∑ v∈V,score v)≤V.card*(V.card+1) at sq
    simpa only [n34] using sq
  have charge (v : ℕ) (hv : v∈V) :
      34+(if v∈V\L then 1 else 0)+(if v∈U then 1 else 0)+(if v∈E then 1 else 0)≤score v := by
    have a := floor_two14 (by decide) free deg hv
    have b := floor_three20 free deg hv
    change 34+(if v∈V\L then 1 else 0)+(if v∈U then 1 else 0)+(if v∈E then 1 else 0)
      ≤(ball G V v 2).card+(ball G V v 3).card
    by_cases e : v∈E
    · have ⟨h1,h2⟩ := eg v e
      split <;> split <;> omega
    by_cases u : v∈U
    · have ⟨h1,h2⟩ := ug v u
      split <;> omega
    · by_cases l : v∈L
      · simp [hv,l,u,e]
        omega
      · have h : (ball G V v 3).card≠20 := fun z => l (mem_filter.mpr ⟨hv,z⟩)
        simp [hv,l,u,e]
        omega
  have budget := coherent_bank_budget lv uv ev charge (d:=0) (by simpa using upper)
  have noK : K.card=0 := by omega
  have noL : L.card=0 := by omega
  have h3 (v) (hv : v∈V) : 21≤(ball G V v 3).card := by
    have b := floor_three20 free deg hv
    by_contra! lt
    have hvL : v∈L := mem_filter.mpr ⟨hv,by omega⟩
    exact (Nat.ne_of_gt (card_pos.mpr ⟨v,hvL⟩)) noL
  have flat (v) (hv : v∈V) : score v=35 := by
    have lo (x) (hx : x∈V) : (35 : ℕ)≤score x := by
      have a := floor_two14 (by decide) free deg hx
      have b := h3 x hx
      change 35≤(ball G V x 2).card+(ball G V x 3).card
      omega
    by_contra neq
    have lt : 35<score v := by have := lo v hv; omega
    have h := sum_lt_sum lo ⟨v,hv,lt⟩
    rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm] at h
    omega
  apply blocked_equal_profile free ho hne
  · intro v hv
    have a := floor_two14 (by decide) free deg hv
    have b := h3 v hv
    have e := flat v hv
    change (ball G V v 2).card+(ball G V v 3).card=35 at e
    omega
  · intro v hv
    have a := floor_two14 (by decide) free deg hv
    have b := h3 v hv
    have e := flat v hv
    change (ball G V v 2).card+(ball G V v 3).card=35 at e
    omega

#print axioms five_free_ge35
end LeanCH.BR.DotDegreeSevenLow


