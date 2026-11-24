import checkpoints.shen_extension.PivotTriangleContraction

namespace LeanCH.BR.Closure.TwoReplacement
open BRq2 BRq3 Finset DotOriginalStarReturn DeficitLevels

/-- Two demands of size d. A common label can serve both demands exactly when
it belongs to F. The overlap is charged once unless it can actually serve twice. -/
theorem assign_heads {A B F : Finset ℕ} {d : ℕ} (fa : F ⊆ A) (fb : F ⊆ B) :
    (∃ C ⊆ A, ∃ E ⊆ B, d ≤ C.card ∧ d ≤ E.card ∧ C ∩ E ⊆ F) ↔
    d ≤ A.card ∧ d ≤ B.card ∧ 2*d ≤ (A ∪ B).card + F.card := by
  classical
  constructor
  · rintro ⟨C,ca,E,eb,hc,he,both⟩
    have u := card_le_card (union_subset_union ca eb)
    have i := card_le_card both
    have parts := card_union_add_card_inter C E
    exact ⟨hc.trans (card_le_card ca),he.trans (card_le_card eb),by omega⟩
  · rintro ⟨ha,hb,capacity⟩
    let overlap := (A ∩ B) \ F
    let cheap := A \ overlap
    have fsub : F ⊆ A ∩ B := subset_inter fa fb
    have oa : overlap ⊆ A := sdiff_subset.trans inter_subset_left
    have ob : overlap ⊆ B := sdiff_subset.trans inter_subset_right
    have one : cheap.card + overlap.card = A.card := card_sdiff_add_card_eq_card oa
    have two : overlap.card + F.card = (A ∩ B).card := card_sdiff_add_card_eq_card fsub
    have unionCard := card_union_add_card_inter A B
    let k := d - cheap.card
    obtain ⟨K,ko,ks⟩ := exists_subset_card_eq (show k ≤ overlap.card by dsimp [k]; omega)
    have dis : Disjoint cheap K := disjoint_left.mpr (fun _ h hk => (mem_sdiff.mp h).2 (ko hk))
    have left : cheap ∪ K ⊆ A := union_subset sdiff_subset (ko.trans oa)
    refine ⟨cheap ∪ K,left,B \ K,sdiff_subset,?_,?_,?_⟩
    · rw [card_union_of_disjoint dis,ks]; dsimp [k]; omega
    · rw [card_sdiff_of_subset (ko.trans ob),ks]; dsimp [k]; omega
    · intro x h
      obtain ⟨ch,r⟩ := mem_inter.mp h
      obtain ⟨xb,notK⟩ := mem_sdiff.mp r
      obtain ⟨xa,no⟩ := mem_sdiff.mp ((mem_union.mp ch).resolve_right notK)
      by_contra notF
      exact no (mem_sdiff.mpr ⟨mem_inter.mpr ⟨xa,xb⟩,notF⟩)

/-- New heads gained by an old row from the two replacement vertices. -/
def credit (P Q : Finset ℕ) (x : ℕ) : ℕ := (if x ∈ P then 1 else 0) + (if x ∈ Q then 1 else 0)

/-- Possible old heads of one or both copies. R is the union of the
corresponding parent sets. Its incident return arcs must be removed. -/
def pool (D : CH.Digraph) (W P Q R : Finset ℕ) (d : ℕ) :=
  (W \ R).filter (fun x => d ≤ (outN D (W \ R) x).card + credit P Q x)

theorem pool_anti {D : CH.Digraph} {W P Q R T : Finset ℕ} {d} (sub : R ⊆ T) :
    pool D W P Q T d ⊆ pool D W P Q R d := by
  intro x hx
  obtain ⟨xt,pay⟩ := mem_filter.mp hx
  have keep : W \ T ⊆ W \ R := fun z hz =>
    mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1,fun zr => (mem_sdiff.mp hz).2 (sub zr)⟩
  have rows : outN D (W \ T) x ⊆ outN D (W \ R) x := fun z hz =>
    mem_outN.mpr ⟨keep (mem_outN.mp hz).1,(mem_outN.mp hz).2⟩
  exact mem_filter.mpr ⟨keep xt,pay.trans (Nat.add_le_add_right (card_le_card rows) _)⟩

def Feasible (D : CH.Digraph) (W P Q : Finset ℕ) (d : ℕ) : Prop :=
  (∀ x ∈ W, d ≤ (outN D W x).card + credit P Q x) ∧
  let A := pool D W P Q P d
  let B := pool D W P Q Q d
  let F := pool D W P Q (P ∪ Q) d
  d ≤ A.card ∧ d ≤ B.card ∧ 2*d ≤ (A ∪ B).card + F.card

/-- All properties of the edited graph that the converse will use. -/
structure Realizes (D E : CH.Digraph) (W P Q : Finset ℕ) (a b d : ℕ) : Prop where
  safe : QFree E (insert b (insert a W)) 3
  degree : ∀ x ∈ insert b (insert a W), d ≤ (outN E (insert b (insert a W)) x).card
  old : ∀ x ∈ W, ∀ z ∈ W, E x z = true → D x z = true
  left : ∀ x ∈ W, E x a = true ↔ x ∈ P
  right : ∀ x ∈ W, E x b = true ↔ x ∈ Q
  independent : E a b ≠ true ∧ E b a ≠ true

private theorem enlarged_row (E : CH.Digraph) {W P Q : Finset ℕ} {a b x : ℕ}
    (fresh : a ∉ W) (fresh' : b ∉ insert a W)
    (pa : E x a = true ↔ x ∈ P) (pb : E x b = true ↔ x ∈ Q) :
    (outN E (insert b (insert a W)) x).card = (outN E W x).card + credit P Q x := by
  have add (T : Finset ℕ) (z : ℕ) (n : z ∉ T) :
      (outN E (insert z T) x).card = (outN E T x).card + (if E x z = true then 1 else 0) := by
    by_cases e : E x z = true
    · have row : outN E (insert z T) x = insert z (outN E T x) := by
        ext h; simp only [mem_outN,mem_insert]; grind
      simp [row,card_insert_of_notMem (fun hit => n (outN_subset hit)),e]
    · have row : outN E (insert z T) x = outN E T x := by
        ext h; simp only [mem_outN,mem_insert]; grind
      simp [row,e]
  rw [add _ _ fresh',add _ _ fresh]
  by_cases l : x ∈ P <;> by_cases r : x ∈ Q <;> simp_all [credit,Nat.add_assoc]

theorem realize {D : CH.Digraph} {W P Q : Finset ℕ} {a b d : ℕ}
    (safe : QFree D W 3) (fresh : a ∉ W) (fresh' : b ∉ insert a W) (pw : P ⊆ W) (qw : Q ⊆ W)
    (test : Feasible D W P Q d) : ∃ E, Realizes D E W P Q a b d := by
  classical
  obtain ⟨base,limits⟩ := test
  obtain ⟨C,ca,L,lb,hc,hl,both⟩ := (assign_heads (pool_anti (R:=P) subset_union_left)
    (pool_anti (R:=Q) subset_union_right)).mpr limits
  have cw : C ⊆ W := ca.trans ((filter_subset _ _).trans sdiff_subset)
  have lw : L ⊆ W := lb.trans ((filter_subset _ _).trans sdiff_subset)
  have pc : Disjoint P C := disjoint_left.mpr (fun _ xp xc => (mem_sdiff.mp (mem_filter.mp (ca xc)).1).2 xp)
  have ql : Disjoint Q L := disjoint_left.mpr (fun _ xq xl => (mem_sdiff.mp (mem_filter.mp (lb xl)).1).2 xq)
  let T := insert a W
  let G := star D W P C a
  let E := star G T Q L b
  have wt : W ⊆ T := subset_insert _ _
  have qt := qw.trans wt
  have lt' := lw.trans wt
  have at' : a ∈ T := mem_insert_self _ _
  have free : QFree E (insert b T) 3 := star_qfree (star_qfree safe fresh pw cw pc) fresh' qt lt' ql
  have oldPair (x) (hx : x ∈ W) (z) (hz : z ∈ W) : E x z = true ↔
      D x z = true ∧ (x ∉ C ∨ z ∉ P) ∧ (x ∉ L ∨ z ∉ Q) := by
    rw [show E x z = true ↔ _ from star_old_edge fresh' (wt hx) (wt hz),
      show G x z = true ↔ _ from star_old_edge fresh hx hz]
    tauto
  have pa (x) (hx : x ∈ W) : E x a = true ↔ x ∈ P := by
    rw [show E x a = true ↔ _ from star_old_edge fresh' (wt hx) at',
      show G x a = true ↔ _ from star_incoming fresh cw]
    simp [show a ∉ Q from fun h => fresh (qw h)]
  have pb (x) (_ : x ∈ W) : E x b = true ↔ x ∈ Q := star_incoming fresh' lt'
  have row (x) (hx : x ∈ W) :
      d ≤ (outN E W x).card + credit P Q x := by
    let R := (if x ∈ C then P else ∅) ∪ (if x ∈ L then Q else ∅)
    have kept : outN D (W \ R) x ⊆ outN E W x := by
      intro z hz
      obtain ⟨zr,e⟩ := mem_outN.mp hz
      obtain ⟨zw,no⟩ := mem_sdiff.mp zr
      refine mem_outN.mpr ⟨zw,(oldPair x hx z zw).mpr ⟨e,?_,?_⟩⟩
      · by_cases xc : x ∈ C
        · exact Or.inr (fun zp => no (mem_union_left _ (by simpa [xc] using zp)))
        · exact Or.inl xc
      · by_cases xl : x ∈ L
        · exact Or.inr (fun zq => no (mem_union_right _ (by simpa [xl] using zq)))
        · exact Or.inl xl
    have price : d ≤ (outN D (W \ R) x).card + credit P Q x := by
      by_cases xc : x ∈ C <;> by_cases xl : x ∈ L
      · simpa [R,xc,xl] using (mem_filter.mp (both (mem_inter.mpr ⟨xc,xl⟩))).2
      · simpa [R,xc,xl] using (mem_filter.mp (ca xc)).2
      · simpa [R,xc,xl] using (mem_filter.mp (lb xl)).2
      · simpa [R,xc,xl] using base x hx
    exact price.trans (Nat.add_le_add_right (card_le_card kept) _)
  refine ⟨E,free,?_,fun x hx z hz e => ((oldPair x hx z hz).mp e).1,pa,pb,?_,?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl|hx
    · apply hl.trans (card_le_card ?_)
      exact fun z hz => mem_outN.mpr ⟨mem_insert_of_mem (lt' hz),(star_outgoing fresh' qt).mpr hz⟩
    rcases mem_insert.mp hx with rfl|xw
    · apply hc.trans (card_le_card ?_)
      intro z hz
      refine mem_outN.mpr ⟨mem_insert_of_mem (wt (cw hz)),(star_old_edge fresh' at' (wt (cw hz))).mpr ?_⟩
      exact ⟨(star_outgoing fresh pw).mpr hz,Or.inl (fun h => fresh (lw h))⟩
    · rw [enlarged_row E fresh fresh' (pa x xw) (pb x xw)]
      exact row x xw
  · exact fun e => fresh (qw ((star_incoming fresh' lt').mp e))
  · exact fun e => fresh (lw ((star_outgoing fresh' qt).mp e))

#print axioms assign_heads
#print axioms realize

/-- Necessity allows arbitrary further deletion of old arcs. Heads that serve
both new vertices must be able to pay the union of the two return cuts. -/
theorem necessary {D E : CH.Digraph} {W P Q : Finset ℕ} {a b d : ℕ}
    (fresh : a ∉ W) (fresh' : b ∉ insert a W) (pw : P ⊆ W) (qw : Q ⊆ W)
    (h : Realizes D E W P Q a b d) : Feasible D W P Q d := by
  classical
  let X := insert b (insert a W)
  have ax : a ∈ X := mem_insert_of_mem (mem_insert_self _ _)
  have bx : b ∈ X := mem_insert_self _ _
  have wx : W ⊆ X := (subset_insert _ _).trans (subset_insert _ _)
  let C := outN E W a
  let L := outN E W b
  have pay (x) (xw : x ∈ W) : d ≤ (outN E W x).card + credit P Q x := by
    have le := h.degree x (wx xw)
    rwa [enlarged_row E fresh fresh' (h.left x xw) (h.right x xw)] at le
  have old (x) (xw : x ∈ W) : outN E W x ⊆ outN D W x := by
    intro z hz
    obtain ⟨zw,e⟩ := mem_outN.mp hz
    exact mem_outN.mpr ⟨zw,h.old x xw z zw e⟩
  have clean (v : ℕ) (vx : v ∈ X) (R : Finset ℕ) (rw' : R ⊆ W)
      (parents : ∀ z ∈ W, E z v = true ↔ z ∈ R) {x} (head : x ∈ outN E W v) :
      x ∈ W \ R ∧ ∀ z ∈ outN E W x, z ∉ R := by
    obtain ⟨xw,vx'⟩ := mem_outN.mp head
    refine ⟨mem_sdiff.mpr ⟨xw,fun xr => digonfree h.safe (by decide) vx (wx xw) vx' ((parents x xw).mpr xr)⟩,?_⟩
    intro z hz zr
    exact h.safe v 3 (by decide) (by decide) (.step (wx xw) vx' (.step (wx (rw' zr)) (mem_outN.mp hz).2
      (.step vx ((parents z (rw' zr)).mpr zr) (.refl _))))
  have enters {x R} (xr : x ∈ W \ R) (no : ∀ z ∈ outN E W x, z ∉ R) : x ∈ pool D W P Q R d := by
    have xw := (mem_sdiff.mp xr).1
    have sub : outN E W x ⊆ outN D (W \ R) x := by
      intro z hz
      exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨outN_subset hz,no z hz⟩,(mem_outN.mp (old x xw hz)).2⟩
    exact mem_filter.mpr ⟨xr,(pay x xw).trans (Nat.add_le_add_right (card_le_card sub) _)⟩
  have left (x) (hx : x ∈ C) := clean a ax P pw h.left hx
  have right (x) (hx : x ∈ L) := clean b bx Q qw h.right hx
  have oldOnly (v : ℕ) (noA : E v a ≠ true) (noB : E v b ≠ true) :
      outN E X v = outN E W v := by
    ext z
    simp only [X,mem_outN,mem_insert]
    grind
  have ca : d ≤ C.card := by
    have le := h.degree a ax
    change d ≤ (outN E X a).card at le
    rwa [oldOnly a (loopfree h.safe (by decide) ax) h.independent.1] at le
  have cb : d ≤ L.card := by
    have le := h.degree b bx
    change d ≤ (outN E X b).card at le
    rwa [oldOnly b h.independent.2 (loopfree h.safe (by decide) bx)] at le
  refine ⟨fun x hx => (pay x hx).trans (Nat.add_le_add_right (card_le_card (old x hx)) _),?_⟩
  apply (assign_heads (pool_anti (R:=P) subset_union_left) (pool_anti (R:=Q) subset_union_right)).mp
  refine ⟨C,fun x hx => enters (left x hx).1 (left x hx).2,L,
    fun x hx => enters (right x hx).1 (right x hx).2,ca,cb,?_⟩
  intro x hx
  obtain ⟨xc,xl⟩ := mem_inter.mp hx
  obtain ⟨xp,avoidP⟩ := left x xc
  obtain ⟨xq,avoidQ⟩ := right x xl
  apply enters
  · exact mem_sdiff.mpr ⟨(mem_sdiff.mp xp).1,fun e => (mem_union.mp e).elim
      (mem_sdiff.mp xp).2 (mem_sdiff.mp xq).2⟩
  · exact fun z hz e => (mem_union.mp e).elim (avoidP z hz) (avoidQ z hz)

theorem exact_test {D : CH.Digraph} {W P Q : Finset ℕ} {a b d : ℕ}
    (safe : QFree D W 3) (fresh : a ∉ W) (fresh' : b ∉ insert a W) (pw : P ⊆ W) (qw : Q ⊆ W) :
    (∃ E, Realizes D E W P Q a b d) ↔ Feasible D W P Q d :=
  ⟨fun ⟨_,h⟩ => necessary fresh fresh' pw qw h,realize safe fresh fresh' pw qw⟩

/-- At native order, after deleting any four labels that kill the short
cycles, every pair of parent banks fails the explicit two-copy test. -/
theorem critical_obstruction {D : CH.Digraph} {U S : Finset ℕ} {d}
    (law : OrderLaw 3 d (3*d+1)) (size : U.card = 3*d+2)
    (sub : S ⊆ U) (four : S.card = 4) (safe : QFree D (U \ S) 3) :
    ∀ P ⊆ U \ S, ∀ Q ⊆ U \ S, ¬ Feasible D (U \ S) P Q d := by
  classical
  intro P pw Q qw test
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < S.card by omega)
  obtain ⟨b,hb⟩ := card_pos.mp (show 0 < (S.erase a).card by rw [card_erase_of_mem ha,four]; decide)
  have fresh : a ∉ U \ S := fun m => (mem_sdiff.mp m).2 ha
  have fresh' : b ∉ insert a (U \ S) := fun m =>
    (mem_insert.mp m).elim (mem_erase.mp hb).1 (fun hit => (mem_sdiff.mp hit).2 (mem_erase.mp hb).2)
  obtain ⟨E,realized⟩ := realize safe fresh fresh' pw qw test
  have bound := law E _ realized.safe realized.degree (insert_nonempty _ _)
  rw [card_insert_of_notMem fresh',card_insert_of_notMem fresh,card_sdiff_of_subset sub,size,four] at bound
  have := card_le_card sub
  omega

#print axioms necessary
#print axioms exact_test
#print axioms critical_obstruction
end LeanCH.BR.Closure.TwoReplacement
