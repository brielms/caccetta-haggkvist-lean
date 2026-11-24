import checkpoints.shen_extension.ReturnBankOrder

namespace LeanCH.BR.Closure.PuncturedRootReturns
open Finset BRq2 BRq3 BR45 DeficitLevels

/-- Original first arcs of four-cycles through h that avoid T at the middle label. -/
def firsts (D : CH.Digraph) (V : Finset ℕ) (h : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (outN D V h).filter (fun a => ∃z∈V\T, D a z=true ∧ (outN D (inN D V h) z).Nonempty)

/-- A first label is counted if its own row sends more than c arcs into T,
or it reaches such an original row outside T which misses h and all its parents. -/
def overloaded (D : CH.Digraph) (V : Finset ℕ) (h : ℕ) (T : Finset ℕ) (c : ℕ) :=
  (outN D V h).filter (fun a => c<(outN D T a).card ∨ ∃z∈V\T, D a z=true ∧
    D z h≠true ∧ (∀i∈inN D V h,D z i≠true) ∧ c<(outN D T z).card)

/-- Even after removing arbitrary neutral middle labels, many distinct
original first arcs must still support four-cycles, provided the number
removed fits the in-degree and order slack. -/
theorem count_affected {s} (O : Origin 3 s) (laws : ∀j<s, OrderLaw 3 j (3*j+1))
    {h : ℕ} (hv : h∈O.V) {T : Finset ℕ} {c : ℕ} (pos : 0<c)
    (tv : T⊆O.V\insert h (inN O.G O.V h ∪ outN O.G O.V h))
    (small : c<s)
    (budget : s+2*c+O.V.card≤3*s+(inN O.G O.V h).card+1+T.card) :
    3*(outN O.G O.V h).card+(inN O.G O.V h).card+T.card+1 ≤
      O.V.card+3*(firsts O.G O.V h T ∪ overloaded O.G O.V h T c).card := by
  classical
  let I := inN O.G O.V h
  let A := outN O.G O.V h
  let B := insert h I
  let W := (O.V\B)\T
  let d := s-c
  let m := 3*d-W.card
  have iv : I⊆O.V := filter_subset _ _
  have av : A⊆O.V := outN_subset
  have bv : B⊆O.V := insert_subset hv iv
  have tsub : T⊆O.V\B := by
    intro z hz
    obtain ⟨zv,notB⟩ := mem_sdiff.mp (tv hz)
    refine mem_sdiff.mpr ⟨zv,fun hit => ?_⟩
    rcases mem_insert.mp hit with rfl|zi
    · exact notB (mem_insert_self _ _)
    · exact notB (mem_insert_of_mem (mem_union_left _ zi))
  have wv : W⊆O.V := sdiff_subset.trans sdiff_subset
  have hi : h∉I := fun hit => loopfree O.free (by decide) hv (mem_inN.mp hit).2
  have bc : B.card=I.card+1 := card_insert_of_notMem hi
  have ord1 := card_sdiff_add_card_eq_card bv
  have ord2 := card_sdiff_add_card_eq_card tsub
  change W.card+T.card=(O.V\B).card at ord2
  change s+2*c+O.V.card≤3*s+I.card+1+T.card at budget
  have bounds : d<s ∧ d≤m ∧ W.card+m=3*d ∧ 0<m := by
    dsimp only [d,m]; omega
  have noH (a) (aa : a∈A) : O.G a h≠true :=
    digonfree O.free (by decide) hv (av aa) (mem_outN.mp aa).2
  have noI (a) (aa : a∈A) (z) (zi : z∈I) : O.G a z≠true := fun az =>
    O.free h 3 (by decide) (by decide) (.step (av aa) (mem_outN.mp aa).2
      (.step (iv zi) az (.step hv (mem_inN.mp zi).2 (.refl _))))
  have aw : A⊆W := by
    intro a aa
    have ah : a≠h := fun e => loopfree O.free (by decide) hv (e ▸ (mem_outN.mp aa).2)
    have ai : a∉I := fun hit => noH a aa (mem_inN.mp hit).2
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨av aa,fun hit => (mem_insert.mp hit).elim ah ai⟩,fun at' => ?_⟩
    exact (mem_sdiff.mp (tv at')).2 (mem_insert_of_mem (mem_union_right _ aa))
  have paid (x) (xv : x∈O.V) (cap : (outN O.G T x).card≤c) (missH : O.G x h≠true) (missI : ∀z∈I,O.G x z≠true) :
      d≤(outN O.G W x).card := by
    have sub : outN O.G O.V x⊆outN O.G W x∪outN O.G T x := by
      intro z hz
      obtain ⟨zv,xz⟩ := mem_outN.mp hz
      by_cases zt : z∈T
      · exact mem_union_right _ (mem_outN.mpr ⟨zt,xz⟩)
      · apply mem_union_left
        apply mem_outN.mpr
        refine ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨zv,?_⟩,zt⟩,xz⟩
        intro zb
        rcases mem_insert.mp zb with rfl|zi
        · exact missH xz
        · exact missI z zi xz
    have le := (card_le_card sub).trans (card_union_le _ _)
    have ge := O.deg x xv
    dsimp only [d]; omega
  let F := firsts O.G O.V h T ∪ overloaded O.G O.V h T c
  have fa : F⊆A := union_subset (filter_subset _ _) (filter_subset _ _)
  have es : A\F⊆ReturnBankOrder.exits O.G W 3 d := by
    intro a ha
    obtain ⟨aa,af⟩ := mem_sdiff.mp ha
    have good : ¬(c<(outN O.G T a).card ∨ ∃z∈O.V\T, O.G a z=true ∧ O.G z h≠true ∧
        (∀i∈I,O.G z i≠true) ∧ c<(outN O.G T z).card) :=
      fun hot => af (mem_union_right _ (mem_filter.mpr ⟨aa,hot⟩))
    refine ReturnBankOrder.triangle_exits.mpr ⟨aw aa,paid a (av aa) (by by_contra! big; exact good (Or.inl big))
      (noH a aa) (noI a aa),?_⟩
    intro z hz
    obtain ⟨zw,az⟩ := mem_outN.mp hz
    have zv := wv zw
    have zh : O.G z h≠true := fun edge => noI a aa z (mem_inN.mpr ⟨zv,edge⟩) az
    have zt := mem_sdiff.mpr ⟨zv,(mem_sdiff.mp zw).2⟩
    have miss (b) (bi : b∈I) (zb : O.G z b=true) : False :=
      af (mem_union_left _ (mem_filter.mpr ⟨aa,z,zt,az,b,mem_outN.mpr ⟨bi,zb⟩⟩))
    exact paid z zv (by by_contra! big; exact good (Or.inr ⟨z,zt,az,zh,miss,big⟩)) zh miss
  have native := ReturnBankOrder.order O (by decide) laws wv
    (Or.inr ⟨bounds.1,bounds.2.2.1.le⟩) (fun x _ => bounds.2.1.trans (Nat.le_add_left _ _))
  have ec := card_le_card es
  have fc := card_sdiff_add_card_eq_card fa
  change 3*A.card+I.card+T.card+1≤O.V.card+3*F.card
  have dtotal : d+c=s := by dsimp [d]; omega
  omega

/-- Even after removing arbitrary neutral middle labels, many distinct
original first arcs must still support four-cycles, provided the number
removed fits the in-degree and order slack. -/
theorem after_row_cost {s} (O : Origin 3 s) (laws : ∀j<s, OrderLaw 3 j (3*j+1))
    {h : ℕ} (hv : h∈O.V) {T : Finset ℕ} {c : ℕ} (pos : 0<c)
    (tv : T⊆O.V\insert h (inN O.G O.V h ∪ outN O.G O.V h))
    (small : c<s)
    (rowCost : ∀x∈O.V, (x∈outN O.G O.V h ∨
       (x∉T ∧ ∃a∈outN O.G O.V h, O.G a x=true)) →
       O.G x h≠true → (∀z∈inN O.G O.V h,O.G x z≠true) →
       (outN O.G T x).card≤c)
    (budget : s+2*c+O.V.card≤3*s+(inN O.G O.V h).card+1+T.card) :
    3*(outN O.G O.V h).card+(inN O.G O.V h).card+T.card+1 ≤
      O.V.card+3*(firsts O.G O.V h T).card := by
  have none : overloaded O.G O.V h T c=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨aa,hot⟩ := mem_filter.mp ha
    rcases hot with own|⟨z,zt,az,zh,zi,big⟩
    · have av := (mem_outN.mp aa).1
      have miss (i) (hi : i∈inN O.G O.V h) (e : O.G a i=true) :=
        O.free h 3 (by decide) (by decide) (.step av (mem_outN.mp aa).2
          (.step (mem_inN.mp hi).1 e (.step hv (mem_inN.mp hi).2 (.refl _))))
      exact own.not_ge (rowCost a av (Or.inl aa)
        (digonfree O.free (by decide) hv av (mem_outN.mp aa).2) miss)
    · exact big.not_ge (rowCost z (mem_sdiff.mp zt).1 (Or.inr ⟨(mem_sdiff.mp zt).2,a,aa,az⟩) zh zi)
  simpa [none] using count_affected O laws hv pos tv small budget

theorem after_removal {s} (O : Origin 3 s) (laws : ∀j<s, OrderLaw 3 j (3*j+1))
    {h : ℕ} (hv : h∈O.V) {T : Finset ℕ} (live : T.Nonempty)
    (tv : T⊆O.V\insert h (inN O.G O.V h ∪ outN O.G O.V h))
    (small : T.card<s) (budget : s+T.card+O.V.card≤3*s+(inN O.G O.V h).card+1) :
    3*(outN O.G O.V h).card+(inN O.G O.V h).card+T.card+1 ≤
      O.V.card+3*(firsts O.G O.V h T).card :=
  after_row_cost O laws hv (card_pos.mpr live) tv small
    (fun _ _ _ _ _ => card_le_card outN_subset) (by omega)

/-- A lower bound on distinct original first labels leading to concentrated rows. -/
theorem majority_count {s} (O : Origin 3 s) (laws : ∀j<s, OrderLaw 3 j (3*j+1))
    {h} (hv : h∈O.V) (high : s≤(inN O.G O.V h).card) {T : Finset ℕ} (live : T.Nonempty)
    (tv : T⊆O.V\insert h (inN O.G O.V h ∪ outN O.G O.V h)) (cut : firsts O.G O.V h T=∅) :
    s+T.card+1≤3*(overloaded O.G O.V h T ((T.card+1)/2)).card := by
  classical
  have iv : inN O.G O.V h⊆O.V := filter_subset _ _
  have av : outN O.G O.V h⊆O.V := outN_subset
  have dis : Disjoint (inN O.G O.V h) (outN O.G O.V h) := disjoint_left.mpr
    (fun _ zi za => digonfree O.free (by decide) hv (iv zi) (mem_outN.mp za).2 (mem_inN.mp zi).2)
  have miss : h∉inN O.G O.V h ∪ outN O.G O.V h := fun z =>
    (mem_union.mp z).elim (fun hi => loopfree O.free (by decide) hv (mem_inN.mp hi).2)
      (fun ha => loopfree O.free (by decide) hv (mem_outN.mp ha).2)
  have c := card_sdiff_add_card_eq_card (insert_subset hv (union_subset iv av))
  rw [card_insert_of_notMem miss,card_union_of_disjoint dis] at c
  have sub := card_le_card tv
  have deg := O.deg h hv
  have ord := O.order
  have pos := card_pos.mpr live
  have test := count_affected O laws hv (c:=(T.card+1)/2) (by omega) tv (by omega) (by omega)
  rw [cut,empty_union] at test
  omega

/-- A first label counted by the return-bank test has an original witness
before T. Different first labels may have the same witness. -/
theorem witness {s} (O : Origin 3 s) {h T a c} (hv : h∈O.V)
    (ha : a∈overloaded O.G O.V h T c) :
    ∃x∈O.V, (x=a ∨ (x∉T ∧ O.G a x=true)) ∧ O.G x h≠true ∧
      (∀z∈inN O.G O.V h,O.G x z≠true) ∧ c<(outN O.G T x).card := by
  obtain ⟨aa,hot⟩ := mem_filter.mp ha
  rcases hot with own|⟨z,zt,az,zh,zi,big⟩
  · have av := (mem_outN.mp aa).1
    refine ⟨a,av,Or.inl rfl,digonfree O.free (by decide) hv av (mem_outN.mp aa).2,?_,own⟩
    intro b bi ab
    exact O.free h 3 (by decide) (by decide) (.step av (mem_outN.mp aa).2
      (.step (mem_inN.mp bi).1 ab (.step hv (mem_inN.mp bi).2 (.refl _))))
  · exact ⟨z,(mem_sdiff.mp zt).1,Or.inr ⟨(mem_sdiff.mp zt).2,az⟩,zh,zi,big⟩

/-- Two witnesses that absorb more than the rounded-up half of T share
at least two actual target labels in T. -/
theorem shared_targets {D : CH.Digraph} {T : Finset ℕ} {x y}
    (hx : (T.card+1)/2<(outN D T x).card) (hy : (T.card+1)/2<(outN D T y).card) :
    2≤(outN D T x∩outN D T y).card := by
  have total := card_union_add_card_inter (outN D T x) (outN D T y)
  have le := card_le_card (union_subset (show outN D T x⊆T from outN_subset)
    (show outN D T y⊆T from outN_subset))
  omega

theorem majority {s} (O : Origin 3 s) (laws : ∀j<s, OrderLaw 3 j (3*j+1))
    {h} (hv : h∈O.V) (high : s≤(inN O.G O.V h).card) {T : Finset ℕ} (live : T.Nonempty)
    (tv : T⊆O.V\insert h (inN O.G O.V h ∪ outN O.G O.V h)) (cut : firsts O.G O.V h T=∅) :
    ∃x∈O.V, (x∈outN O.G O.V h ∨ (x∉T ∧ ∃a∈outN O.G O.V h,O.G a x=true)) ∧
      O.G x h≠true ∧ (∀z∈inN O.G O.V h,O.G x z≠true) ∧
      (T.card+1)/2 < (outN O.G T x).card := by
  have num := majority_count O laws hv high live tv cut
  obtain ⟨a,ha⟩ := card_pos.mp (show 0<(overloaded O.G O.V h T ((T.card+1)/2)).card by omega)
  obtain ⟨x,xv,near,mh,mi,big⟩ := witness O hv ha
  refine ⟨x,xv,?_,mh,mi,big⟩
  have aa := (mem_filter.mp ha).1
  rcases near with rfl|⟨xt,ax⟩
  · exact Or.inl aa
  · exact Or.inr ⟨xt,a,aa,ax⟩

#print axioms majority_count
#print axioms shared_targets
#print axioms witness
#print axioms count_affected
#print axioms majority
#print axioms after_row_cost
#print axioms after_removal
end LeanCH.BR.Closure.PuncturedRootReturns
