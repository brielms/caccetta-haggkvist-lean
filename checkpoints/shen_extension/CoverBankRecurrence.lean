import checkpoints.shen_extension.TwoBankDescent

namespace LeanCH.BR.Closure.CoverBankRecurrence
open Finset BRq2 BRq3 BR45 DeficitLevels

/-- Tight exterior rows covering every vertex of S. -/
def parents (D : CH.Digraph) (V S : Finset ℕ) (s : ℕ) : Finset ℕ :=
  (V\S).filter (fun p => (outN D V p).card=s ∧ S⊆outN D V p)

private theorem row_split {D : CH.Digraph} {V B : Finset ℕ} (sub : B⊆V) (x : ℕ) :
    (outN D (V\B) x).card+(outN D B x).card=(outN D V x).card := by
  have eq : outN D (V\B) x=outN D V x\outN D B x := by
    ext z; simp only [mem_sdiff,mem_outN]; tauto
  rw [eq,card_sdiff_add_card_eq_card (show outN D B x⊆outN D V x from
    fun z hz => mem_outN.mpr ⟨sub (mem_outN.mp hz).1,(mem_outN.mp hz).2⟩)]

private theorem seen {D : CH.Digraph} (B : Finset ℕ) (x : ℕ) :
    (outN D B x).card≤(if (outN D B x).Nonempty then B.card else 0) := by
  split_ifs with a
  · exact card_le_card outN_subset
  · rw [not_nonempty_iff_eq_empty.mp a,card_empty]

/-- Shrinking either side of a complete two-bank chain must leave a specific
original row short. The ordering of the two edits protects the girth. -/
private theorem short {q s} (O : Origin q s) (hq : 2≤q) {S H k l}
    (sv : S⊆O.V) (hw : H⊆O.V\S) (exits : ∀a∈S, ∀h∈H, O.G a h=true)
    (live : S.Nonempty) (small : k+l<S.card+(parents O.G O.V S s).card)
    (innerS : q*(s-H.card)<k) (innerP : q*(s-k)<l) :
    let P := parents O.G O.V S s
    let W := (O.V\S)\P
    ∃x∈W, (outN O.G W x).card+(if (outN O.G S x).Nonempty then k else 0)
       +(if (outN O.G P x).Nonempty then l else 0)<s := by
  classical
  let P := parents O.G O.V S s
  let W := (O.V\S)\P
  change ∃x∈W, _ 
  have pv : P⊆O.V\S := filter_subset _ _
  have all (p) (hp : p∈P) : S⊆outN O.G O.V p := (mem_filter.mp hp).2.2
  obtain ⟨a,ha⟩ := live
  have common : H⊆W := by
    intro h hh
    apply mem_sdiff.mpr
    refine ⟨hw hh,fun hp => ?_⟩
    exact digonfree O.free hq (sv ha) (mem_sdiff.mp (hw hh)).1 (exits a ha h hh)
      (mem_outN.mp (all h hp ha)).2
  have feeds (p) (hp : p∈P) : (outN O.G S p).Nonempty :=
    ⟨a,mem_outN.mpr ⟨ha,(mem_outN.mp (all p hp ha)).2⟩⟩
  by_contra! paid
  obtain ⟨G,U,ne,uc,free,deg⟩ := TwoBankDescent.funded O.free (by omega : 1≤q)
    (show W⊆O.V from sdiff_subset.trans sdiff_subset) sv (pv.trans sdiff_subset) common
    (empty_subset W) exits (by simp) feeds innerS (by simpa using innerP) paid
  have ord := O.least G U free deg ne
  have tot := card_sdiff_add_card_eq_card sv
  have tot2 := card_sdiff_add_card_eq_card pv
  change W.card+P.card=(O.V\S).card at tot2
  change k+l<S.card+P.card at small
  omega

/-- A wide common-exit bank forces tight covering parents, and the number
of all such parents is bounded by the internal cost of the second bank. -/
theorem parent_capacity {q s} (O : Origin q s) (hq : 2≤q) {S H}
    (sv : S⊆O.V) (hw : H⊆O.V\S) (exits : ∀a∈S, ∀h∈H, O.G a h=true)
    (width : q*(s-H.card)+2≤S.card) :
    let P := parents O.G O.V S s
    0<P.card ∧ P.card≤q*(s-(S.card-1)) := by
  classical
  let P := parents O.G O.V S s
  let W := (O.V\S)\P
  obtain ⟨p,pv,tight,all⟩ := CommonExitReplacement.covering_parent O (by omega) sv hw exits width
  have hp : p∈P := mem_filter.mpr ⟨pv,tight,all⟩
  refine ⟨card_pos.mpr ⟨p,hp⟩,?_⟩
  by_contra! many
  obtain ⟨x,xw,under⟩ := short O hq sv hw exits (card_pos.mp (by omega))
    (k:=S.card-1) (l:=P.card) (by change _<S.card+P.card; omega) (by omega) many
  have xv := (mem_sdiff.mp (mem_sdiff.mp xw).1).1
  have xp := (mem_sdiff.mp xw).2
  have cs := card_le_card (show outN O.G S x⊆S from outN_subset)
  have cp := seen (D:=O.G) P x
  have eq1 := row_split (D:=O.G) sv x
  have eq2 := row_split (D:=O.G) (show P⊆O.V\S from filter_subset _ _) x
  change (outN O.G W x).card+(if (outN O.G S x).Nonempty then S.card-1 else 0)+(if (outN O.G P x).Nonempty then P.card else 0)<s at under
  change (outN O.G W x).card+_= _ at eq2
  have deg := O.deg x xv
  by_cases hit : (outN O.G S x).Nonempty
  · simp only [hit,ite_true] at under
    have same := eq_of_subset_of_card_le (show outN O.G S x⊆S from outN_subset) (by omega)
    apply xp
    exact mem_filter.mpr ⟨(mem_sdiff.mp xw).1,by omega,fun z hz => by
      obtain ⟨zs,xz⟩ := mem_outN.mp (same.symm ▸ hz : z∈outN O.G S x)
      exact mem_outN.mpr ⟨sv zs,xz⟩⟩
  · simp only [hit,ite_false] at under
    rw [not_nonempty_iff_eq_empty.mp hit,card_empty] at eq1
    omega

#print axioms parent_capacity

/-- Moving the one deleted label from S to its covering parents forces a
second tight covering row. It avoids every vertex of S. -/
theorem next_parent {q s} (O : Origin q s) (hq : 2≤q) {S H}
    (sv : S⊆O.V) (hw : H⊆O.V\S) (exits : ∀a∈S, ∀h∈H, O.G a h=true)
    (width : q*(s-H.card)+2≤S.card) (size : S.card=s)
    (plural : 2≤(parents O.G O.V S s).card) :
    let P := parents O.G O.V S s
    ∃x∈(O.V\S)\P, (outN O.G O.V x).card=s ∧ P⊆outN O.G O.V x ∧ outN O.G S x=∅ := by
  classical
  let P := parents O.G O.V S s
  let W := (O.V\S)\P
  change 2≤P.card at plural
  obtain ⟨x,xw,under⟩ := short O hq sv hw exits (card_pos.mp (by omega))
    (k:=s) (l:=P.card-1) (by change _<S.card+P.card; omega) (by omega) (by simp; omega)
  have xv := (mem_sdiff.mp (mem_sdiff.mp xw).1).1
  have eq1 := row_split (D:=O.G) sv x
  have eq2 := row_split (D:=O.G) (show P⊆O.V\S from filter_subset _ _) x
  have cs := card_le_card (show outN O.G S x⊆S from outN_subset)
  have cp := card_le_card (show outN O.G P x⊆P from outN_subset)
  have deg := O.deg x xv
  change (outN O.G W x).card+(if (outN O.G S x).Nonempty then s else 0)+(if (outN O.G P x).Nonempty then P.card-1 else 0)<s at under
  change (outN O.G W x).card+_= _ at eq2
  have miss : ¬(outN O.G S x).Nonempty := by
    intro hit
    simp only [hit,ite_true] at under
    omega
  have z := not_nonempty_iff_eq_empty.mp miss
  simp only [miss,ite_false] at under
  rw [z,card_empty] at eq1
  have ph : (outN O.G P x).Nonempty := by
    by_contra absent
    rw [not_nonempty_iff_eq_empty.mp absent,card_empty] at eq2
    omega
  simp only [ph,ite_true] at under
  have full := eq_of_subset_of_card_le (show outN O.G P x⊆P from outN_subset) (by omega)
  refine ⟨x,xw,by omega,?_,z⟩
  intro a ha
  obtain ⟨ap,xa⟩ := mem_outN.mp (full.symm ▸ ha : a∈outN O.G P x)
  exact mem_outN.mpr ⟨(mem_sdiff.mp (mem_filter.mp ap).1).1,xa⟩

#print axioms next_parent

end LeanCH.BR.Closure.CoverBankRecurrence
