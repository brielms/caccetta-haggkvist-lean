import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5BankGeometry_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- A tight root's entire second bank is a six-cycle with a common spill,
and its third layer has a shared six-label exterior witness. -/
theorem tight_spill_geometry {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (e3 : (ball D V u 3).card=20) :
    let A := (ball D V u 1).erase u
    let B := ball D V u 2 \ ball D V u 1
    let T := ball D V u 3 \ ball D V u 2
    B.card=6 ∧ T.card=6 ∧ OutEq 1 D B ∧
    (∀ b∈B, outN D V b ⊆ B ∪ T) ∧
    (∀ b∈B, ∀ t∈T, D b t=true) ∧
    ∃ t∈T, ∃ S : Finset ℕ, S.card=6 ∧ S⊆V \ ball D V u 3 ∧
      ∀ w∈S, D t w=true := by
  classical
  have e2 := tight_three_only_tight_two hf ho hu e3
  let A := (ball D V u 1).erase u
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  let U := (ball D V u 2).erase u
  have dm : ∀ v∈V,7≤(outN D V v).card := fun _ hv => (ho _ hv).ge
  obtain ⟨_,cb,M,P,_,_,_,_,_,_,reach⟩ := six_bank_first_layer hf ho hu e2
  change B.card=6 at cb
  change (∀ a∈A, ∃ p∈A, ∃ i≤2, Walk D V a p i ∧ ∀ b∈B, D p b=true) at reach
  have ct : T.card=6 := by
    have s := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    change T.card+(ball D V u 2).card=(ball D V u 3).card at s
    omega
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have tv : T⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have bu : B⊆U := by
    intro x hx
    refine mem_erase.mpr ⟨?_,(mem_sdiff.mp hx).1⟩
    intro e
    subst x
    exact (mem_sdiff.mp hx).2 (self_mem_ball hu)
  have join : A∪B=U := (erase_ball_succ_eq_union (k:=1) hu).symm
  have noBA (b) (hb : b∈B) (a) (ha : a∈A) : D b a≠true := by
    intro ba
    obtain ⟨p,_,i,ib,walk,pb⟩ := reach a ha
    exact hf b (i+1+1) (by omega) (by omega)
      (Walk.step (av ha) ba (walk.snoc (bv hb) (pb b hb)))
  have keep (b) (hb : b∈B) : outN D V b ⊆ outN D B b ∪ outN D T b := by
    intro x hx
    have base := outN_prefix_loss hf hu (by decide : 2+1≤5) (bu hb) hx
    rcases mem_union.mp base with h|h
    · obtain ⟨xU,arc⟩ := mem_outN.mp h
      change x∈U at xU
      rw [←join] at xU
      rcases mem_union.mp xU with ha|hb'
      · exact (noBA b hb x ha arc).elim
      · exact mem_union_left _ (mem_outN.mpr ⟨hb',arc⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨h,(mem_outN.mp hx).2⟩)
  have bMin (b) (hb : b∈B) : 1≤(outN D B b).card := by
    have h := (dm b (bv hb)).trans ((card_le_card (keep b hb)).trans (card_union_le _ _))
    have c := card_le_card (outN_subset (D:=D) (W:=T) (y:=b))
    omega
  obtain ⟨_,MB,lb,_,subB,cbm,eqB⟩ := exists_minimal_cycle_support
    (by decide : 1≤5) (hf.mono_set bv) bMin (card_pos.mp (by omega))
  have eq : MB=B := eq_of_subset_of_card_le subB (by omega)
  have one : OutEq 1 D B := eq ▸ eqB
  have bfull (b) (hb : b∈B) (t) (ht : t∈T) : D b t=true := by
    have c := (dm b (bv hb)).trans ((card_le_card (keep b hb)).trans (card_union_le _ _))
    have o := one b hb
    have all : outN D T b=T := eq_of_subset_of_card_le outN_subset (by omega)
    exact (mem_outN.mp (all.symm ▸ ht)).2
  refine ⟨cb,ct,one,?_,bfull,?_⟩
  · intro b hb w hw
    rcases mem_union.mp (keep b hb hw) with h|h
    · exact mem_union_left _ (outN_subset h)
    · exact mem_union_right _ (outN_subset h)
  have find : ∃ t∈T, (outN D T t).card≤1 := by
    by_contra! all
    have h := corB (U:=T) (by decide : 1≤5) (hf.mono_set tv)
      (fun v hv => all v hv) (card_pos.mp (by omega))
    change 2*5+1≤T.card at h
    omega
  obtain ⟨t,ht,td⟩ := find
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<B.card by omega)
  let H := outN D V t \ T
  have H6 : 6≤H.card := by
    have sub : outN D T t⊆outN D V t := fun v h =>
      mem_outN.mpr ⟨tv (mem_outN.mp h).1,(mem_outN.mp h).2⟩
    have eq : outN D V t \ H=outN D T t := by
      ext v
      simp only [H,mem_sdiff,mem_outN]
      constructor
      · rintro ⟨⟨hv,e⟩,h⟩
        exact ⟨by by_contra n; exact h ⟨⟨hv,e⟩,n⟩,e⟩
      · rintro ⟨hv,e⟩
        exact ⟨⟨tv hv,e⟩,fun h => h.2 hv⟩
    have sp := card_sdiff_add_card_eq_card (sdiff_subset (s:=outN D V t) (t:=T))
    change (outN D V t \ H).card+H.card=(outN D V t).card at sp
    rw [eq,ho t (tv ht)] at sp
    omega
  obtain ⟨S,SH,s6⟩ := exists_subset_card_eq H6
  refine ⟨t,ht,S,s6,?_,fun w hw => (mem_outN.mp (mem_sdiff.mp (SH hw)).1).2⟩
  intro w hw
  obtain ⟨wV,tw⟩ := mem_outN.mp (mem_sdiff.mp (SH hw)).1
  refine mem_sdiff.mpr ⟨wV,?_⟩
  intro w3
  have nwT := (mem_sdiff.mp (SH hw)).2
  have w2 : w∈ball D V u 2 := by
    by_contra n
    exact nwT (mem_sdiff.mpr ⟨w3,n⟩)
  by_cases wu : w=u
  · subst w
    obtain ⟨_,i,ib,walk⟩ := mem_ball.mp (mem_sdiff.mp ht).1
    exact hf u (i+1) (by omega) (by omega) (walk.snoc hu tw)
  have wU : w∈U := mem_erase.mpr ⟨wu,w2⟩
  rw [←join] at wU
  rcases mem_union.mp wU with wa|wb
  · obtain ⟨p,_,i,ib,walk,pB⟩ := reach w wa
    have a := (walk.snoc (bv hb) (pB b hb)).snoc (tv ht) (bfull b hb t ht)
    exact hf w (i+1+1+1) (by omega) (by omega) (a.snoc wV tw)
  · exact hf w 2 (by decide) (by decide)
      (.step (tv ht) (bfull w wb t ht) (.step wV tw (.refl w)))

#print axioms tight_spill_geometry
end LeanCH.BR.DotDegreeSevenLow


