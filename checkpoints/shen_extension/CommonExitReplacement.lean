import checkpoints.shen_extension.PaidLayerDescent
import LeanCH.BR.BRClosedNeighborhoodRepair

namespace LeanCH.BR.Closure.CommonExitReplacement
open BRq2 BRq3 Finset DeficitLevels

/-- Old rows with at least one head in S can feed the replacement. All
replacement labels use common old exits H. Inside K the graph is F. -/
def edited (D F : CH.Digraph) (S K H : Finset ℕ) : CH.Digraph := fun x y =>
  if x∈K then (if y∈K then F x y else decide (y∈H))
  else if y∈K then decide ((outN D S x).Nonempty) else D x y

private def represents (K S : Finset ℕ) (x a : ℕ) : Prop :=
  if x∈K then a∈S else a=x

/-- A mixed walk may pause while inside K. Its first entrant chooses the
original representative, which can leave by every allowed exit. A mixed
closed walk thereby gives a positive old closed walk without lengthening. -/
private theorem project {D F V S K H W x y n}
    (sv : S⊆V) (wv : W⊆V)
    (exits : ∀a∈S, ∀ h∈H, D a h=true)
    (path : Walk (edited D F S K H) (W∪K) x y n) (xU : x∈W∪K) :
    (x∈K ∧ y∈K ∧ Walk F K x y n) ∨
    ∃ b, represents K S y b ∧ ∀ a, represents K S x a →
      ∃ l≤n, (0<n ∨ x∈K → 0<l) ∧ Walk D V a b l := by
  induction path with
  | refl x =>
    by_cases xk : x∈K
    · exact Or.inl ⟨xk,xk,.refl _⟩
    · exact Or.inr ⟨x,by simp [represents,xk],fun a ha => by
        have eq : a=x := by simpa [represents,xk] using ha
        subst a; exact ⟨0,le_rfl,by simp [xk],.refl _⟩⟩
  | @step x y z n yU edge tail ih =>
    rcases ih yU with ⟨yk,zk,internal⟩ | ⟨b,zb,projectTail⟩
    · by_cases xk : x∈K
      · exact Or.inl ⟨xk,zk,.step yk (by simpa [edited,xk,yk] using edge) internal⟩
      · have hit : (outN D S x).Nonempty := by simpa [edited,xk,yk] using edge
        obtain ⟨b,hb⟩ := hit
        exact Or.inr ⟨b,by simpa [represents,zk] using (mem_outN.mp hb).1,fun a ha => by
          have eq : a=x := by simpa [represents,xk] using ha
          subst a; exact ⟨1,by omega,by simp,.step (sv (mem_outN.mp hb).1) (mem_outN.mp hb).2 (.refl _)⟩⟩
    · right
      refine ⟨b,zb,?_⟩
      intro a ha
      by_cases yk : y∈K
      · by_cases xk : x∈K
        · have ay : represents K S y a := by simpa [represents,yk,xk] using ha
          obtain ⟨l,le,positive,w⟩ := projectTail a ay
          exact ⟨l,by omega,fun _ => positive (Or.inr yk),w⟩
        · have hit : (outN D S x).Nonempty := by simpa [edited,xk,yk] using edge
          obtain ⟨p,ph⟩ := hit
          obtain ⟨l,le,_,w⟩ := projectTail p (by simpa [represents,yk] using (mem_outN.mp ph).1)
          have eq : a=x := by simpa [represents,xk] using ha
          subst a
          exact ⟨l+1,by omega,by omega,.step (sv (mem_outN.mp ph).1) (mem_outN.mp ph).2 w⟩
      · obtain ⟨l,le,_,w⟩ := projectTail y (by simp [represents,yk])
        have yv := wv ((mem_union.mp yU).resolve_right yk)
        refine ⟨l+1,by omega,by omega,.step yv ?_ w⟩
        by_cases xk : x∈K
        · exact exits a (by simpa [represents,xk] using ha) y (by simpa [edited,xk,yk] using edge)
        · have eq : a=x := by simpa [represents,xk] using ha
          simpa [eq,edited,xk,yk] using edge

theorem safe {D F V S K H W q} (original : QFree D V q) (internal : QFree F K q)
    (sv : S⊆V) (wv : W⊆V) (exits : ∀a∈S, ∀ h∈H, D a h=true) :
    QFree (edited D F S K H) (W∪K) q := by
  intro x n pos le path
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  obtain ⟨_,_,xu,_⟩ := path.unsnoc
  rcases project sv wv exits path xu with ⟨_,_,w⟩|⟨b,xb,step⟩
  · exact internal x _ pos le w
  · obtain ⟨l,lt,lp,w⟩ := step b xb
    exact original b l (lp (Or.inl pos)) (lt.trans le) w

/-- Exact payment for the edit, permitting an arbitrary q-free internal
graph and a different entering witness for each original parent. -/
theorem host {D F V S K H W q d} (original : QFree D V q) (internal : QFree F K q)
    (sv : S⊆V) (wv : W⊆V) (sep : Disjoint W K) (hw : H⊆W)
    (exits : ∀a∈S, ∀ h∈H, D a h=true)
    (old : ∀x∈W, d≤(outN D W x).card+(if (outN D S x).Nonempty then K.card else 0))
    (newRows : ∀x∈K, d≤(outN F K x).card+H.card) :
    ∃ E, QFree E (W∪K) q ∧ ∀x∈W∪K, d≤(outN E (W∪K) x).card := by
  let E := edited D F S K H
  refine ⟨E,safe original internal sv wv exits,?_⟩
  intro x hx
  rcases mem_union.mp hx with xw|xk
  · have xk := disjoint_left.mp sep xw
    have inOld : outN D W x⊆outN E (W∪K) x := by
      intro y hy
      obtain ⟨yw,xy⟩ := mem_outN.mp hy
      exact mem_outN.mpr ⟨mem_union_left _ yw,by simpa [E,edited,xk,disjoint_left.mp sep yw] using xy⟩
    have pay := old x xw
    by_cases hit : (outN D S x).Nonempty
    · have inK : K⊆outN E (W∪K) x := fun y yk => mem_outN.mpr
        ⟨mem_union_right _ yk,by simp [E,edited,xk,yk,hit]⟩
      have count := card_le_card (union_subset inOld inK)
      rw [card_union_of_disjoint (sep.mono_left outN_subset)] at count
      exact (by simpa [hit] using pay : d≤(outN D W x).card+K.card).trans count
    · exact (by simpa [hit] using pay : d≤(outN D W x).card).trans (card_le_card inOld)
  · have inF : outN F K x⊆outN E (W∪K) x := by
      intro y hy
      obtain ⟨yk,xy⟩ := mem_outN.mp hy
      exact mem_outN.mpr ⟨mem_union_right _ yk,by simpa [E,edited,xk,yk] using xy⟩
    have inH : H⊆outN E (W∪K) x := fun y yh => mem_outN.mpr ⟨mem_union_left _ (hw yh),
      by simp [E,edited,xk,disjoint_left.mp sep (hw yh),yh]⟩
    have count := card_le_card (union_subset inF inH)
    rw [card_union_of_disjoint ((sep.symm.mono_left outN_subset).mono_right hw)] at count
    exact (newRows x xk).trans count

/-- A fresh bank of exactly m labels paying e heads internally at any
cutoff. A closed walk of q or fewer steps cannot wind round the circle. -/
theorem fresh_bank (W : Finset ℕ) {q e m : ℕ} (hq : 1≤q) (room : q*e<m) :
    ∃ (F : CH.Digraph) (K : Finset ℕ), K.card=m ∧ Disjoint W K ∧ QFree F K q ∧
      ∀x∈K, (outN F K x).card=e := by
  let b := W.sup id+1
  let K := (range m).image (fun i => b+i)
  let heads (x : ℕ) := (Icc 1 e).image (fun i => b+((x-b+i)%m))
  let F : CH.Digraph := fun x y => decide (y∈heads x)
  have pos : 0<m := by omega
  have lt : e<m := by have := Nat.mul_le_mul_right e hq; simpa only [one_mul] using this.trans_lt room
  have sub (x) : heads x⊆K := by
    rintro y hy
    obtain ⟨i,_,rfl⟩ := mem_image.mp hy
    exact mem_image.mpr ⟨_,mem_range.mpr (Nat.mod_lt _ pos),rfl⟩
  have eq (x) : outN F K x=heads x := by
    ext y; simp only [mem_outN,F,decide_eq_true_eq,and_iff_right_iff_imp]; exact fun h => sub x h
  have disj : Disjoint W K := by
    apply disjoint_left.mpr; intro x xw xk
    obtain ⟨i,_,hi⟩ := mem_image.mp xk
    have le : x ≤ W.sup id := le_sup (f:=id) xw
    dsimp only [b] at hi; omega
  have kc : K.card=m := by
    change ((range m).image (fun i => b+i)).card=m
    rw [card_image_of_injective _ (fun _ _ t => Nat.add_left_cancel t),card_range]
  refine ⟨F,K,kc,disj,qfree_of_bounded_modular_steps room (fun x => x-b) ?_,?_⟩
  · intro x _ y _ xy
    obtain ⟨i,hi,yi⟩ := mem_image.mp (of_decide_eq_true xy : y∈heads x)
    refine ⟨i,(mem_Icc.mp hi).1,(mem_Icc.mp hi).2,?_⟩
    change (x-b+i)%m=(y-b)%m
    rw [←yi,Nat.add_sub_cancel_left,Nat.mod_mod]
  · intro x _
    rw [eq]
    dsimp only [heads]
    rw [card_image_iff.mpr]
    · simp
    · intro i hi j hj same
      have mod : Nat.ModEq m (x-b+i) (x-b+j) := Nat.add_left_cancel same
      have im := (mem_Icc.mp hi).2.trans_lt lt
      have jm := (mem_Icc.mp hj).2.trans_lt lt
      simpa only [Nat.ModEq,Nat.mod_eq_of_lt im,Nat.mod_eq_of_lt jm] using mod.add_left_cancel' (x-b)

/-- The numeric certificate constructs a smaller-degree host itself. The
intermediaries S may lie anywhere in the original graph, including W. -/
theorem funded {D V W H S q d m} (original : QFree D V q) (hq : 1≤q)
    (sv : S⊆V) (wv : W⊆V) (hw : H⊆W) (exits : ∀a∈S, ∀h∈H, D a h=true)
    (room : q*(d-H.card)<m)
    (paid : ∀x∈W, d≤(outN D W x).card+(if (outN D S x).Nonempty then m else 0)) :
    ∃ E U, U.Nonempty ∧ U.card=W.card+m ∧ QFree E U q ∧ ∀x∈U, d≤(outN E U x).card := by
  obtain ⟨F,K,km,sep,free,rows⟩ := fresh_bank W hq room
  obtain ⟨E,ef,ed⟩ := host original free sv wv sep hw exits
    (by simpa only [km] using paid) (fun x xk => by rw [rows x xk]; omega)
  have live : K.Nonempty := card_pos.mp (by omega)
  exact ⟨E,W∪K,live.mono subset_union_right,by rw [card_union_of_disjoint sep,km],ef,ed⟩

#print axioms safe

/-- At least order, a bank with enough common exits can lose one label.
The only possible obstruction is an original tight exterior row that sees
every member of the bank. The bank need not be a module. -/
theorem covering_parent {q s} (O : Origin q s) (hq : 1≤q) {S H : Finset ℕ}
    (sv : S⊆O.V) (hw : H⊆O.V\S) (exits : ∀a∈S, ∀h∈H, O.G a h=true)
    (width : q*(s-H.card)+2≤S.card) :
    ∃x∈O.V\S, (outN O.G O.V x).card=s ∧ S⊆outN O.G O.V x := by
  classical
  let W := O.V\S
  let m := S.card-1
  by_contra none
  have paid (x) (xw : x∈W) : s≤(outN O.G W x).card+
      (if (outN O.G S x).Nonempty then m else 0) := by
    have eq : outN O.G W x = outN O.G O.V x \ outN O.G S x := by
      ext z; simp only [W,mem_sdiff,mem_outN]; tauto
    have inc : outN O.G S x ⊆ outN O.G O.V x := fun z hz =>
      mem_outN.mpr ⟨sv (mem_outN.mp hz).1,(mem_outN.mp hz).2⟩
    have split := card_sdiff_add_card_eq_card inc
    rw [←eq] at split
    have dm := O.deg x (mem_sdiff.mp xw).1
    have limit := card_le_card (show outN O.G S x⊆S from outN_subset)
    split_ifs with hit
    · by_contra! short
      dsimp only [m] at short
      have same := eq_of_subset_of_card_le (show outN O.G S x⊆S from outN_subset) (by omega)
      exact none ⟨x,xw,by omega,same ▸ inc⟩
    · have z := not_nonempty_iff_eq_empty.mp hit
      rw [z,card_empty] at split
      omega
  obtain ⟨E,U,ne,uc,free,deg⟩ := funded O.free hq sv (show W⊆O.V from sdiff_subset) hw exits
    (show q*(s-H.card)<m by dsimp [m]; omega) paid
  have bigger := O.least E U free deg ne
  have total := card_sdiff_add_card_eq_card sv
  change W.card+S.card=O.V.card at total
  dsimp only [m] at uc
  omega

/-- The two sides of any common-exit rectangle are constrained even when
the rows inside the left side have very different internal arcs. -/
theorem bank_limit {q s} (O : Origin q s) (hq : 1≤q) {S H : Finset ℕ}
    (sv : S⊆O.V) (hw : H⊆O.V\S) (exits : ∀a∈S, ∀h∈H, O.G a h=true)
    (tooMany : s<S.card) : S.card≤q*(s-H.card)+1 := by
  by_contra! width
  obtain ⟨x,_,tight,all⟩ := covering_parent O hq sv hw exits (by omega)
  have size := card_le_card all
  omega

/-- At a regular-size unmatched incoming column, the whole set of its
common exits is bounded. A tight row covering this column would equal it. -/
theorem unmatched_limit {q s} (O : Origin q s) (hq : 1≤q) {y H}
    (size : (BR45.inN O.G O.V y).card=s)
    (unmatched : ∀x∈O.V,(outN O.G O.V x).card=s → outN O.G O.V x≠BR45.inN O.G O.V y)
    (hv : H⊆O.V) (exits : ∀a∈BR45.inN O.G O.V y, ∀h∈H, O.G a h=true) :
    s≤q*(s-H.card)+1 := by
  by_contra! wide
  have hw : H⊆O.V\BR45.inN O.G O.V y := fun h hh => mem_sdiff.mpr
    ⟨hv hh,fun hy => loopfree O.free hq (hv hh) (exits h hy h hh)⟩
  have width : q*(s-H.card)+2≤(BR45.inN O.G O.V y).card := by rw [size]; omega
  obtain ⟨x,xw,tight,sub⟩ := covering_parent O hq (filter_subset _ _) hw exits width
  have sameSize : (outN O.G O.V x).card≤(BR45.inN O.G O.V y).card := by rw [tight,size]
  exact unmatched x (mem_sdiff.mp xw).1 tight (eq_of_subset_of_card_le sub sameSize).symm

#print axioms host
#print axioms funded
#print axioms covering_parent
#print axioms bank_limit
#print axioms unmatched_limit
end LeanCH.BR.Closure.CommonExitReplacement
