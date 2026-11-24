import checkpoints.shen_extension.ReceiverPrivateExits

/-!
# One labelled root for the receiver packet

A receiver packet is an existential statement. Each theorem that opens it
names its own root, and Lean has no proof that two such roots agree. Here
the packet is opened once. Every later rule takes the root, the full head
and the marked return as explicit arguments, so its conclusion is about the
vertices already in the family. The earlier theorems that each reopen the
packet at a root of their own remain available to ordinary proofs. Replay
no longer applies them.

Nothing below depends on a particular degree. The law enters through its
shell size and through the count of heavily missed shell columns.
-/

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 CHRuleCatalog AvoidedHeadQuota BoundaryTightParentReach

/-- Open the packet once. The root, the heavy head, the exceptional shell
column and the head it returns to are all named here. -/
theorem receiver_root {D : CH.Digraph} {U : Finset ℕ} {law : ReceiverLaw} (witness : law.on D U) :
    ∃v∈U,∃h∈outN D U v,∃z∈ball D U v 2 \ ball D U v 1,∃b∈outN D U v,
      (inN D U v).card=law.parents ∧ (ball D U v 2 \ ball D U v 1).card=law.shell ∧
      (∑a∈outN D U v,(law.degree-(inN D U a).card))≤law.charge ∧
      law.lowerCount≤((ball D U v 2 \ ball D U v 1).filter
        fun z=>law.missing≤(outN D U v\inN D U z).card).card ∧
      ((ball D U v 2 \ ball D U v 1).filter
        fun z=>law.missing≤(outN D U v\inN D U z).card).card≤law.upperCount ∧
      law.degree≤(inN D U h).card ∧ law.missing≤(outN D U v\inN D U z).card ∧
      D h z=true ∧ D z b=true := by
  obtain ⟨y,ym,parents,sz,charge,low,high,h,hm,heavy,z,zm,hz,b,bm,zb⟩ := physical witness
  obtain ⟨zy,miss⟩ := mem_filter.mp zm
  exact ⟨y,ym,h,hm,z,zy,b,bm,parents,sz,charge,low,high,heavy,miss,hz,zb⟩

/-- At a root that carries the count, an actual head covers the whole shell. -/
theorem marked_full_head {D : CH.Digraph} {V : Finset ℕ} {q v : ℕ} {law : ReceiverLaw}
    (free : QFree D V q) (vm : v∈V) (reg : OutEq law.degree D V)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount)
    (size : (ball D V v 2\ball D V v 1).card=law.shell)
    (many : law.lowerCount≤((ball D V v 2\ball D V v 1).filter
      fun z=>law.missing≤(outN D V v\inN D V z).card).card) :
    ∃g∈outN D V v,(ball D V v 2\ball D V v 1)⊆outN D V g ∧
      (outN D (outN D V v) g).card+(ball D V v 2\ball D V v 1).card=law.degree := by
  classical
  obtain ⟨cut,two,region,mult,cost,cover⟩ := fit
  have br := WeightedSD.boundary_regular_outside_pressure_region cut two region
  let H:=outN D V v
  let Y:=ball D V v 2\ball D V v 1
  let X:=Y.filter fun z=>law.missing≤(H\inN D V z).card
  have cap : law.degree*(Y.card+(law.degree-1)/q-law.degree)<X.card*law.missing := by
    change Y.card=law.shell at size
    rw [size]
    exact cost.trans_le (Nat.mul_le_mul_right _ many)
  obtain ⟨g,gm,light⟩ := light_head free (by omega) vm reg mult br (X:=X) (filter_subset ..)
    (fun a am=>(mem_filter.mp am).2) cap
  change (outN D H g).card<(law.degree-1)/q at light
  have id := missing_count free (by omega) vm gm (reg g (mem_outN.mp gm).1)
  change (Y\outN D V g).card+law.degree=Y.card+(outN D H g).card at id
  change Y.card=law.shell at size
  have empty : (Y\outN D V g).card=0 := by omega
  exact ⟨g,gm,sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp empty),
    (show (outN D H g).card+Y.card=law.degree by omega)⟩

/-- A shell vertex seen by `g` never returns to `g` itself. -/
theorem return_avoids_full {D : CH.Digraph} {V : Finset ℕ} {q v g z b : ℕ} (free : QFree D V q)
    (cut : 3≤q) (gm : g∈outN D V v) (full : (ball D V v 2\ball D V v 1)⊆outN D V g)
    (zm : z∈ball D V v 2\ball D V v 1) (zb : D z b=true) : b≠g := by
  intro same
  subst b
  exact digonfree free (by omega) (mem_outN.mp gm).1 (ball_subset (mem_sdiff.mp zm).1)
    (mem_outN.mp (full zm)).2 zb

/-- The head it returns to does not point back to `g`. -/
theorem return_not_back {D : CH.Digraph} {V : Finset ℕ} {q v g z b : ℕ} (free : QFree D V q)
    (cut : 3≤q) (gm : g∈outN D V v) (full : (ball D V v 2\ball D V v 1)⊆outN D V g)
    (zm : z∈ball D V v 2\ball D V v 1) (bm : b∈outN D V v) (zb : D z b=true) : D b g≠true := by
  intro bg
  have gv := (mem_outN.mp gm).1
  exact free g 3 (by decide) cut (.step (ball_subset (mem_sdiff.mp zm).1) (mem_outN.mp (full zm)).2
    (.step (mem_outN.mp bm).1 zb (.step gv bg (.refl _))))

/-- The fork at this root and this full head. Either another actual head
also covers the shell, or `g` is the only one and every return it misses
comes back to it inside the head bank in exactly `q-1` arcs.

The statement holds at every full head. Replay applies it at the head whose
row count is on record. The first alternative names a further full head with
no proof that it is new, so applying the rule to that head again would
produce the same alternative without end. -/
theorem marked_fork {D : CH.Digraph} {V : Finset ℕ} {q v g : ℕ} {law : ReceiverLaw}
    (free : QFree D V q) (vm : v∈V) (reg : OutEq law.degree D V)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount)
    (one : law.shell+(law.degree-1)/q=law.degree+1)
    (size : (ball D V v 2\ball D V v 1).card=law.shell)
    (many : law.lowerCount≤((ball D V v 2\ball D V v 1).filter
      fun z=>law.missing≤(outN D V v\inN D V z).card).card)
    (gm : g∈outN D V v) (full : (ball D V v 2\ball D V v 1)⊆outN D V g)
    (_row : (outN D (outN D V v) g).card+(ball D V v 2\ball D V v 1).card=law.degree) :
    (1<((outN D V v).filter fun a=>(ball D V v 2\ball D V v 1)⊆outN D V a).card ∧
        ∃a∈outN D V v,a≠g ∧ (ball D V v 2\ball D V v 1)⊆outN D V a) ∨
      (((outN D V v).filter fun a=>(ball D V v 2\ball D V v 1)⊆outN D V a)={g} ∧
        ∀z∈ball D V v 2\ball D V v 1,∀b∈outN D V v,D z b=true → D g b≠true →
          Walk D (outN D V v) b g (q-1)) := by
  classical
  obtain ⟨cut,two,region,mult,cost,cover⟩ := fit
  have br := WeightedSD.boundary_regular_outside_pressure_region cut two region
  let H:=outN D V v
  let Y:=ball D V v 2\ball D V v 1
  let X:=Y.filter fun z=>law.missing≤(H\inN D V z).card
  have cap : law.degree*(Y.card+(law.degree-1)/q-law.degree)<X.card*law.missing := by
    change Y.card=law.shell at size
    rw [size]
    exact cost.trans_le (Nat.mul_le_mul_right _ many)
  have excess := high_head free (by omega) vm reg (X:=X) (filter_subset ..)
    (fun s sm=>(mem_filter.mp sm).2) cap
  have fork := full_or_returns free (by omega) vm reg gm mult br (by rw [size]; exact one) full excess
  by_cases more : ∃a∈H,a≠g ∧ Y⊆outN D V a
  · obtain ⟨a,ah,ne,af⟩ := more
    exact Or.inl ⟨one_lt_card.mpr ⟨a,mem_filter.mpr ⟨ah,af⟩,g,mem_filter.mpr ⟨gm,full⟩,ne⟩,a,ah,ne,af⟩
  · refine Or.inr ⟨?_,fork.resolve_left more⟩
    apply eq_singleton_iff_unique_mem.mpr
    exact ⟨mem_filter.mpr ⟨gm,full⟩,fun a am=>by
      by_contra diff
      exact more ⟨a,(mem_filter.mp am).1,diff,(mem_filter.mp am).2⟩⟩

attribute [aesop safe forward (immediate := [witness]) (rule_sets := [CHGraphFamilies])] receiver_root
ch_family_split_result receiver_root
attribute [aesop safe forward (immediate := [free,vm,reg,fit,size,many])
  (rule_sets := [CHGraphFamilies])] marked_full_head
ch_family_split_result marked_full_head
attribute [aesop safe forward (immediate := [free,cut,gm,full,zm,zb])
  (rule_sets := [CHGraphFamilies])] return_avoids_full
attribute [aesop safe forward (immediate := [free,cut,gm,full,zm,bm,zb])
  (rule_sets := [CHGraphFamilies])] return_not_back
attribute [aesop safe forward (immediate := [free,vm,reg,fit,one,size,many,gm,full,_row])
  (rule_sets := [CHGraphFamilies])] marked_fork
ch_family_split_result marked_fork

/-- Ask replay to decide the window on this packet's own numbers. -/
theorem ready_window {D : CH.Digraph} {U : Finset ℕ} {q : ℕ} {law : ReceiverLaw} (_witness : law.on D U)
    (_free : QFree D U q) :
    FullWindow q law.degree law.shell law.missing law.lowerCount →
    FullWindow q law.degree law.shell law.missing law.lowerCount := id

attribute [aesop safe forward (immediate := [_witness,_free]) (rule_sets := [CHGraphFamilies])] ready_window

#print axioms receiver_root
#print axioms marked_full_head
#print axioms return_avoids_full
#print axioms return_not_back
#print axioms marked_fork
end LeanCH.BR.LabelledCompromiseRecipe
