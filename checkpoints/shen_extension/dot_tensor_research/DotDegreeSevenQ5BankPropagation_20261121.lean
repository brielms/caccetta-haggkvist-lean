import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5BankPacking_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen
open scoped BigOperators

structure SpillStep (D : CH.Digraph) (V B T : Finset ℕ) : Prop where
  subB : B⊆V
  subT : T⊆V
  sixB : B.card=6
  sixT : T.card=6
  apart : Disjoint B T
  one : OutEq 1 D B
  keep : ∀ b∈B, outN D V b⊆B∪T
  full : ∀ b∈B, ∀ t∈T, D b t=true

/-- The common spill of an actual bank is another bank if the two-balls
through the bank are capped at 15. -/
theorem spillStep_next {D : CH.Digraph} {V B T : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V)
    (cap : ∀ v∈V, (ball D V v 2).card≤15)
    (h : SpillStep D V B T) : ∃ S, SpillStep D V T S := by
  classical
  let S := T.biUnion (fun x => outN D V x \ T)
  have sv : S⊆V := by
    intro a ha
    obtain ⟨t,ht,hm⟩ := mem_biUnion.mp ha
    exact (mem_outN.mp (mem_sdiff.mp hm).1).1
  have ts : Disjoint T S := disjoint_left.mpr (by
    intro a at' as'
    obtain ⟨t,ht,hm⟩ := mem_biUnion.mp as'
    exact (mem_sdiff.mp hm).2 at')
  have bs : Disjoint B S := disjoint_left.mpr (by
    intro a ab ar
    obtain ⟨t,ht,hm⟩ := mem_biUnion.mp ar
    have ta := (mem_outN.mp (mem_sdiff.mp hm).1).2
    exact hf a 2 (by decide) (by decide)
      (.step (h.subT ht) (h.full a ab t ht) (.step (h.subB ab) ta (.refl a))))
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<B.card by rw [h.sixB]; decide)
  let I := ball D B b 2
  have ib : I⊆B := ball_subset
  have iv : I⊆ball D V b 2 := by
    intro x hx
    obtain ⟨xB,i,hi,w⟩ := mem_ball.mp hx
    exact mem_ball.mpr ⟨h.subB xB,i,hi,w.mono h.subB⟩
  have i3 : 3≤I.card := ball_one_growth (hf.mono_set h.subB)
    (fun v hv => (h.one v hv).ge) hb 2 (by decide)
  have tv : T⊆ball D V b 2 := fun t ht =>
    mem_ball.mpr ⟨h.subT ht,1,by decide,.step (h.subT ht) (h.full b hb t ht) (.refl t)⟩
  have sb : S⊆ball D V b 2 := by
    intro x hx
    obtain ⟨t,ht,hm⟩ := mem_biUnion.mp hx
    obtain ⟨xv,e⟩ := mem_outN.mp (mem_sdiff.mp hm).1
    exact mem_ball.mpr ⟨xv,2,by decide,
      .step (h.subT ht) (h.full b hb t ht) (.step xv e (.refl x))⟩
  have mx := card_le_card (union_subset (union_subset iv tv) sb)
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨bs.mono_left ib,ts⟩),
    card_union_of_disjoint (h.apart.mono_left ib),h.sixT] at mx
  have s6 : S.card≤6 := by have k := cap b (h.subB hb); omega
  have keep (t) (ht : t∈T) : outN D V t⊆T∪S := by
    intro x hx
    by_cases e : x∈T
    · exact mem_union_left _ e
    · exact mem_union_right _ (mem_biUnion.mpr ⟨t,ht,mem_sdiff.mpr ⟨hx,e⟩⟩)
  have ct (t) (ht : t∈T) :
      7=(outN D T t).card+(outN D S t).card := by
    have em : outN D V t=outN D (T∪S) t := by
      ext x
      simp only [mem_outN]
      exact ⟨fun h' => ⟨keep t ht (mem_outN.mpr h'),h'.2⟩,
        fun h' => ⟨union_subset h.subT sv h'.1,h'.2⟩⟩
    rw [← card_outN_union ts,←em,ho t (h.subT ht)]
  have md (t) (ht : t∈T) : 1≤(outN D T t).card := by
    have d := ct t ht
    have e := card_le_card (outN_subset (D:=D) (W:=S) (y:=t))
    omega
  have oneT : OutEq 1 D T := (dt_reg (by decide : 1≤5) (ball_q_one 5 (by decide))
    (hf.mono_set h.subT) md (by simpa only [Nat.mul_one,Nat.reduceAdd] using h.sixT)).1
  have sixOut (t) (ht : t∈T) : (outN D S t).card=6 := by
    have e := ct t ht
    rw [oneT t ht] at e
    omega
  obtain ⟨t,ht⟩ := card_pos.mp (show 0<T.card by rw [h.sixT]; decide)
  have s6' : S.card=6 := by
    have e := card_le_card (outN_subset (D:=D) (W:=S) (y:=t))
    rw [sixOut t ht] at e
    omega
  refine ⟨S, h.subT,sv,h.sixT,s6',ts,oneT,keep,?_⟩
  intro t ht x hx
  have e : outN D S t=S := eq_of_subset_of_card_le outN_subset (by rw [s6',sixOut t ht])
  exact (mem_outN.mp (e.symm ▸ hx)).2

private theorem spill_walk {D : CH.Digraph} {V : Finset ℕ} {F : ℕ→Finset ℕ}
    (h : ∀ i, SpillStep D V (F i) (F (i+1))) (i k : ℕ) (hk : 0<k)
    {a b : ℕ} (ha : a∈F i) (hb : b∈F (i+k)) :
    Walk D V a b k := by
  induction k generalizing b with
  | zero => omega
  | succ k ih =>
    by_cases eq : k=0
    · subst k
      exact .step ((h i).subT hb) ((h i).full a ha b hb) (.refl b)
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<(F (i+k)).card by rw [(h (i+k)).sixB]; decide)
    have p := ih (Nat.pos_of_ne_zero eq) hx
    exact p.snoc ((h (i+k)).subT hb) ((h (i+k)).full x hx b hb)

/-- A single full spill bank would recursively occupy at least 36 vertices. -/
theorem no_spill_bank_at35 {D : CH.Digraph} {V B T : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card≤35)
    (cap : ∀ v∈V, (ball D V v 2).card≤15)
    (h : SpillStep D V B T) : False := by
  classical
  let next : {s : Finset ℕ × Finset ℕ // SpillStep D V s.1 s.2} →
      {s : Finset ℕ × Finset ℕ // SpillStep D V s.1 s.2} :=
    fun s => ⟨(s.val.2,(spillStep_next hf ho cap s.property).choose),
      (spillStep_next hf ho cap s.property).choose_spec⟩
  let st : ℕ → {s : Finset ℕ × Finset ℕ // SpillStep D V s.1 s.2} :=
    Nat.rec ⟨(B,T),h⟩ (fun _ s => next s)
  let F (i : ℕ) := (st i).val.1
  have step (i) : SpillStep D V (F i) (F (i+1)) := (st i).property
  have diff (i j : ℕ) (ij : i<j) (jt : j<6) : F i≠F j := by
    intro eq
    obtain ⟨b,hb⟩ := card_pos.mp (show 0<(F i).card by rw [(step i).sixB]; decide)
    have last : b∈F (i+(j-i)) := by rw [show i+(j-i)=j by omega,←eq]; exact hb
    exact hf b (j-i) (by omega) (by omega) (spill_walk step i (j-i) (by omega) hb last)
  have dis : (↑(range 6) : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj ne
    have i6 := mem_range.mp (show i∈range 6 from hi)
    have j6 := mem_range.mp (show j∈range 6 from hj)
    have di : F i≠F j := by
      rcases lt_or_gt_of_ne ne with lt|lt
      · exact diff i j lt j6
      · exact (diff j i lt i6).symm
    exact (spill_banks_disjoint_or_equal hf (step i).subB (step j).subB
      (step i).sixB (step j).sixB (step i).one (step j).one
      (step i).keep (step j).keep (step i).full (step j).full).resolve_right di
  have sv : (range 6).biUnion F⊆V := biUnion_subset.mpr (fun i _ => (step i).subB)
  have sz := card_le_card sv
  rw [card_biUnion dis] at sz
  have eq : (∑ i∈range 6,(F i).card)=36 := by
    calc
      _ = ∑ _i∈range 6,(6 : ℕ) := sum_congr rfl (fun i _ => (step i).sixB)
      _ = 36 := by simp
  omega

#print axioms spillStep_next
#print axioms no_spill_bank_at35
end LeanCH.BR.DotDegreeSevenLow

