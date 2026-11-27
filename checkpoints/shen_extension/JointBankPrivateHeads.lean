import checkpoints.shen_extension.JointBankGeometry

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45

/-- Two rows have both a common head and distinct private heads, with neither
private head equal to the other row. -/
structure PrivateFork (D : CH.Digraph) (V : Finset ℕ) where
  x : ℕ
  j : ℕ
  h : ℕ
  p : ℕ
  g : ℕ
  xv : x ∈ V
  jv : j ∈ V
  xh : h ∈ outN D V x
  jh : h ∈ outN D V j
  xp : p ∈ outN D V x
  jp : p ∉ outN D V j
  pj : p ≠ j
  jg : g ∈ outN D V j
  xg : g ∉ outN D V x
  gx : g ≠ x

private theorem hit_by_packing {D V q s} (free : QFree D V q) (live : V.Nonempty)
    (reg : OutEq s D V) (pos : 0 < s) (room : V.card ≤ q*s)
    (hit : ∀ u ∈ V, ∃ a ∈ outN D V u, ∀ v ∈ V,
      (outN D V u ∩ outN D V v).Nonempty → a ∈ outN D V v) : False := by
  classical
  let H := outN D V
  let F := V.powerset.filter (fun S : Finset ℕ => (S : Set ℕ).PairwiseDisjoint H)
  have empty : ∅ ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp⟩
  obtain ⟨S,sm,top⟩ := F.exists_max_image card ⟨∅,empty⟩
  have sv := mem_powerset.mp (mem_filter.mp sm).1
  have dis : (S : Set ℕ).PairwiseDisjoint H := (mem_filter.mp sm).2
  have cover (v) (vv : v ∈ V) : ∃ u ∈ S, (H u ∩ H v).Nonempty := by
    by_contra! no
    have own : (H v).Nonempty := card_pos.mp ((reg v vv).symm ▸ pos)
    have vn : v ∉ S := fun vm => by
      have e := no v vm
      exact own.ne_empty (by simpa using e)
    have keep : insert v S ∈ F := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset_iff.mpr ⟨vv,sv⟩),?_⟩
      rw [coe_insert,Set.pairwiseDisjoint_insert]
      refine ⟨dis,fun u us _ => disjoint_left.mpr ?_⟩
      intro h hv hu
      have hz := mem_inter.mpr ⟨hu,hv⟩
      rw [no u us] at hz
      exact notMem_empty _ hz
    have big := top _ keep
    rw [card_insert_of_notMem vn] at big
    omega
  let pick (u : ℕ) := if huv : u∈V then (hit u huv).choose else u
  have picked (u : ℕ) (uv : u∈V) :
      pick u ∈ H u ∧ ∀v∈V,(H u ∩ H v).Nonempty → pick u ∈ H v := by
    simpa [pick,uv,H] using (hit u uv).choose_spec
  let Z := S.image pick
  have zsub : Z ⊆ V := by
    intro a az
    obtain ⟨u,us,rfl⟩ := mem_image.mp az
    exact outN_subset (picked u (sv us)).1
  have meets (v) (vv : v∈V) : ∃ z∈Z, z∈H v := by
    obtain ⟨u,us,meet⟩ := cover v vv
    exact ⟨pick u,mem_image_of_mem _ us,(picked u (sv us)).2 _ vv meet⟩
  have nonempty : Z.Nonempty := by
    obtain ⟨v,vv⟩ := live
    obtain ⟨z,zm,_⟩ := meets v vv
    exact ⟨z,zm⟩
  have un : S.biUnion H ⊆ V := fun a ha => by
    obtain ⟨u,_,hu⟩ := mem_biUnion.mp ha
    exact outN_subset hu
  have bound := card_le_card un
  rw [card_biUnion dis,sum_congr rfl (fun u us => reg u (sv us)),sum_const,smul_eq_mul] at bound
  have sc := Nat.le_of_mul_le_mul_right (bound.trans room) pos
  have zc : Z.card ≤ q := card_image_le.trans sc
  obtain ⟨v,vm,sink⟩ := exists_sink (free.mono_set zsub) nonempty zc
  obtain ⟨z,zm,edge⟩ := meets v (zsub vm)
  exact sink _ zm (mem_outN.mp edge).2

/-- If no private fork exists, overlapping distinct rows are almost equal.
Three distinct row neighbourhoods cannot overlap pairwise in such a graph. -/
theorem exists_privateFork {D V q s} (free : QFree D V q) (live : V.Nonempty)
    (reg : OutEq s D V) (hs : 3 ≤ s) (hq : 3 ≤ q) (room : V.card ≤ q*s) :
    Nonempty (PrivateFork D V) := by
  classical
  by_contra none
  let H := outN D V
  let step (a b : ℕ) := D a b = true ∧ ∀ z ∈ H a, z ≠ b → z ∈ H b
  have decidePair {a b} (av : a∈V) (bv : b∈V) (meet : (H a ∩ H b).Nonempty)
      (diff : H a ≠ H b) : step a b ∨ step b a := by
    obtain ⟨h,hm⟩ := meet
    have lack (u v : ℕ) (uv : u∈V) (vv : v∈V) (ne : H u ≠ H v) : ∃z∈H u, z∉H v := by
      by_contra! sub
      exact ne (eq_of_subset_of_card_le sub ((reg v vv).trans (reg u uv).symm).le)
    by_cases pr : ∃p∈H a, p∉H b ∧ p≠b
    · obtain ⟨p,pa,pb,pne⟩ := pr
      have cover : ∀g∈H b, g≠a → g∈H a := by
        intro g gb gn
        by_contra ga
        exact none ⟨⟨a,b,h,p,g,av,bv,(mem_inter.mp hm).1,(mem_inter.mp hm).2,pa,pb,pne,gb,ga,gn⟩⟩
      obtain ⟨g,gb,ga⟩ := lack b a bv av diff.symm
      have eq : g=a := by_contra fun ne => ga (cover g gb ne)
      exact Or.inr ⟨eq ▸ (mem_outN.mp gb).2,cover⟩
    · have cover (p) (pa : p∈H a) (pn : p≠b) : p∈H b := by_contra fun no => pr ⟨p,pa,no,pn⟩
      obtain ⟨p,pa,pb⟩ := lack a b av bv diff
      have eq : p=b := by_contra fun ne => pb (cover p pa ne)
      exact Or.inl ⟨eq ▸ (mem_outN.mp pa).2,cover⟩
  have loss {a b} (av : a∈V) (bv : b∈V) (meet : (H a ∩ H b).Nonempty) :
      (H a \ H b).card ≤ 1 := by
    by_cases same : H a=H b
    · simp [same]
    have one {u v} (st : step u v) : (H u \ H v).card ≤ 1 := by
      have sub : H u \ H v ⊆ {v} := by
        intro z zm
        apply mem_singleton.mpr
        exact by_contra fun ne => (mem_sdiff.mp zm).2 (st.2 z (mem_sdiff.mp zm).1 ne)
      simpa using card_le_card sub
    rcases decidePair av bv meet same with st|st
    · exact one st
    · have e1 := card_sdiff_add_card_inter (H a) (H b)
      have e2 := card_sdiff_add_card_inter (H b) (H a)
      rw [inter_comm (H b),show (H b).card=s from reg b bv] at e2
      rw [show (H a).card=s from reg a av] at e1
      have h := one st
      omega
  have noThree {a b c} (av : a∈V) (bv : b∈V) (cv : c∈V)
      (ab : step a b ∨ step b a) (bc : step b c ∨ step c b) (ac : step a c ∨ step c a) : False := by
    have cycle {u v w} (uv : u∈V) (vv : v∈V) (wv : w∈V) (f : step u v) (g : step v w)
        (h : step w u) : False := free u 3 (by decide) hq
          (.step vv f.1 (.step wv g.1 (.step uv h.1 (.refl _))))
    have linear {u v w} (vv : v∈V) (wv : w∈V) (f : step u v) (g : step v w) (h : step u w) : False := by
      have vw : v≠w := fun e => loopfree free (by omega) wv (e ▸ g.1)
      have back := h.2 v (mem_outN.mpr ⟨vv,f.1⟩) vw
      exact digonfree free (by omega) vv wv g.1 (mem_outN.mp back).2
    rcases ab with ab|ba <;> rcases bc with bc|cb <;> rcases ac with ac|ca
    all_goals first
      | exact cycle av bv cv ab bc ca
      | exact cycle cv bv av cb ba ac
      | exact linear bv cv ab bc ac
      | exact linear cv bv ac cb ab
      | exact linear av cv ba ac bc
      | exact linear cv av bc ca ba
      | exact linear av bv ca ab cb
      | exact linear bv av cb ba ca
  apply hit_by_packing free live reg (by omega) room
  intro a av
  by_cases distinct : ∃ b∈V,(H a ∩ H b).Nonempty ∧ H a≠H b
  · obtain ⟨b,bv,ab,abne⟩ := distinct
    obtain ⟨h,hh⟩ := ab
    refine ⟨h,(mem_inter.mp hh).1,?_⟩
    intro c cv ac
    by_cases eq : H a=H c
    · change h ∈ H c; rw [← eq]; exact (mem_inter.mp hh).1
    by_cases eq' : H b=H c
    · change h ∈ H c; rw [← eq']; exact (mem_inter.mp hh).2
    have bc : (H b ∩ H c).Nonempty := by
      by_contra! empty
      have sub : H a ⊆ (H a \ H b) ∪ (H a \ H c) := by
        intro z za
        by_cases zb : z∈H b
        · apply mem_union_right
          apply mem_sdiff.mpr
          refine ⟨za,fun zc => ?_⟩
          have impossible := mem_inter.mpr ⟨zb,zc⟩
          rw [empty] at impossible
          exact notMem_empty _ impossible
        · exact mem_union_left _ (mem_sdiff.mpr ⟨za,zb⟩)
      have bound := (card_le_card sub).trans (card_union_le ..)
      have l1 := loss av bv ⟨h,hh⟩
      have l2 := loss av cv ac
      have sz : (H a).card=s := reg a av
      omega
    exact False.elim (noThree av bv cv (decidePair av bv ⟨h,hh⟩ abne)
      (decidePair bv cv bc eq') (decidePair av cv ac eq))
  · obtain ⟨h,ha⟩ := card_pos.mp ((reg a av).symm ▸ (by omega : 0<s))
    refine ⟨h,ha,fun b bv ab => ?_⟩
    have eq : H a=H b := by_contra fun ne => distinct ⟨b,bv,ab,ne⟩
    change h ∈ H b; rw [← eq]; exact ha

#print axioms exists_privateFork
end LeanCH.BR.BypassBankReplay

