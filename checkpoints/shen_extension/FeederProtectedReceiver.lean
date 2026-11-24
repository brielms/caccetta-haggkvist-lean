import checkpoints.shen_extension.FeederPrivateHeadRepair

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent

open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights

/-- Positive strict prices on the native least source require an exclusive head
in each direction between distinct rows, also when the two rows are nonadjacent. -/
theorem has_exclusive {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {π c} (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {a b} (av : a ∈ X.V) (bv : b ∈ X.V) (ne : a ≠ b) :
    (exclusive X.D X.V a b).Nonempty := by
  classical
  have kept : b ∈ X.V.erase a := mem_erase.mpr ⟨ne.symm,bv⟩
  have nonneg j (jv : j ∈ X.V.erase a) : 0 ≤ transferWeight π a b j := by
    unfold transferWeight
    split_ifs <;> linarith [pos j (mem_of_mem_erase jv),pos a av]
  obtain ⟨j,jv,low⟩ := small _ _ (card_erase_lt_of_mem av)
    (X.free.reverse.mono_set (erase_subset a X.V)) _ nonneg ⟨b,kept⟩
  have cls := (EqualizerTransfer.classify hq X.free.reverse small (fun i hi => (pos i hi).le)
    high cols av bv ne jv).2
  by_contra empty
  apply (not_lt_of_ge low)
  apply cls.mpr
  rintro ⟨aj,bj⟩
  apply empty
  exact ⟨j,mem_sdiff.mpr ⟨mem_outN.mpr ⟨mem_of_mem_erase jv,aj⟩,
    fun h => Bool.noConfusion (bj.symm.trans (mem_outN.mp h).2)⟩⟩

/-- Any preassigned subsets fitting on both sides can be covered before the
actual bijection is chosen. Their labels can never be left unmatched. -/
theorem cover_labels {A B P Q : Finset ℕ} (pa : P ⊆ A) (qb : Q ⊆ B)
    (pb : P.card ≤ B.card) (qa : Q.card ≤ A.card) :
    ∃ m : Matching A B, P ⊆ m.left ∧ Q ⊆ m.right := by
  classical
  by_cases h : A.card ≤ B.card
  · obtain ⟨R,qr,rb,eq⟩ := exists_subsuperset_card_eq qb qa h
    exact ⟨⟨A,R,Subset.rfl,rb,equivOfCardEq eq.symm,Or.inl rfl⟩,pa,qr⟩
  · obtain ⟨L,pl,la,eq⟩ := exists_subsuperset_card_eq pa pb (le_of_not_ge h)
    exact ⟨⟨L,B,la,Subset.rfl,equivOfCardEq eq,Or.inr rfl⟩,pl,qb⟩

/-- An actual unpaid leftover label reached by matching from the specified seed. -/
def exposedAt {q : ℕ} (D : CH.Digraph) (V : Finset ℕ) (w π : ℕ → ℚ)
    (ell : ℕ) (seed : Pair) (j : ℕ) : Prop :=
  ∃ policy : Policy D V, ∃ y ∈ V ×ˢ V,
    Relation.ReflTransGen (Rises policy w ell) seed y ∧
    w y.1 ≠ w y.2 ∧ (outN D V y.1).card ≠ (outN D V y.2).card ∧
    padicNorm ell (gap w y) < padicNorm ell (remainder (policy y.1 y.2) w) ∧
    ((j ∈ exclusive D V y.1 y.2 \ (policy y.1 y.2).left ∧ failsTransfer q D V π y.1 y.2 j) ∨
     (j ∈ exclusive D V y.2 y.1 \ (policy y.1 y.2).right ∧ failsTransfer q D V π y.2 y.1 j))

/-- On a single strict source a prescribed label can always be protected from
being the final unmatched bill. Terminal rows may depend on the protected label. -/
theorem escape_label {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {w π c} (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {ell : ℕ} [Fact ell.Prime] (divides : ell ∣ q) {a b} (av : a ∈ X.V) (bv : b ∈ X.V)
    (diff : w a ≠ w b) (z : ℕ) :
    ∃ j, j ≠ z ∧ exposedAt (q := q) X.D X.V w π ell (a,b) j := by
  classical
  have policy_exists (u v : ℕ) :
      ∃ m : Matching (exclusive X.D X.V u v) (exclusive X.D X.V v u),
        u ∈ X.V → v ∈ X.V → u ≠ v →
          z ∉ exclusive X.D X.V u v \ m.left ∧ z ∉ exclusive X.D X.V v u \ m.right := by
    by_cases ok : u ∈ X.V ∧ v ∈ X.V ∧ u ≠ v
    · let A := exclusive X.D X.V u v
      let B := exclusive X.D X.V v u
      have ap : 0 < A.card := card_pos.mpr (has_exclusive X hq small pos high cols ok.1 ok.2.1 ok.2.2)
      have bp : 0 < B.card := card_pos.mpr (has_exclusive X hq small pos high cols ok.2.1 ok.1 ok.2.2.symm)
      have one (T : Finset ℕ) : (T ∩ {z}).card ≤ 1 := by
        simpa using (card_le_card (inter_subset_right : T ∩ {z} ⊆ {z}))
      obtain ⟨m,hA,hB⟩ := cover_labels (inter_subset_left : A ∩ {z} ⊆ A)
        (inter_subset_left : B ∩ {z} ⊆ B) ((one A).trans bp) ((one B).trans ap)
      exact ⟨m,fun _ _ _ => ⟨fun h => (mem_sdiff.mp h).2 (hA (mem_inter.mpr ⟨(mem_sdiff.mp h).1,mem_singleton_self z⟩)),
        fun h => (mem_sdiff.mp h).2 (hB (mem_inter.mpr ⟨(mem_sdiff.mp h).1,mem_singleton_self z⟩))⟩⟩
    · exact ⟨chooseMatching _ _,fun hu hv ne => (ok ⟨hu,hv,ne⟩).elim⟩
  choose policy protects using policy_exists
  obtain ⟨y,yv,path,ne,degrees,rank,unpaid⟩ := marked_repair X hq small flat pos high cols divides policy av bv diff
  have safe := protects y.1 y.2 (mem_product.mp yv).1 (mem_product.mp yv).2 (fun eq => ne (congrArg w eq))
  rcases unpaid with ⟨j,remains,bill⟩ | ⟨j,remains,bill⟩
  · exact ⟨j,fun eq => safe.1 (eq ▸ remains),policy,y,yv,path,ne,degrees,rank,Or.inl ⟨remains,bill⟩⟩
  · exact ⟨j,fun eq => safe.2 (eq ▸ remains),policy,y,yv,path,ne,degrees,rank,Or.inr ⟨remains,bill⟩⟩

theorem two_labels {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {w π c} (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {ell : ℕ} [Fact ell.Prime] (divides : ell ∣ q) {a b} (av : a ∈ X.V) (bv : b ∈ X.V)
    (diff : w a ≠ w b) :
    ∃ j k, j ≠ k ∧ exposedAt (q := q) X.D X.V w π ell (a,b) j ∧
      exposedAt (q := q) X.D X.V w π ell (a,b) k := by
  have escape := escape_label X hq small flat pos high cols divides av bv diff
  obtain ⟨j,_,hj⟩ := escape a
  obtain ⟨k,hk,hk'⟩ := escape j
  exact ⟨j,k,hk.symm,hj,hk'⟩

/-- Remember arbitrarily many actual labels through all substitutions. An unpaid
column outside that set is exposed unless at this very terminal pair the remembered
private heads on one side outnumber the entire opposite private bank. -/
theorem remembered_set {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {w π c} (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {ell : ℕ} [Fact ell.Prime] (divides : ell ∣ q) {a b} (av : a ∈ X.V) (bv : b ∈ X.V)
    (diff : w a ≠ w b) (H : Finset ℕ) :
    ∃ policy : Policy X.D X.V, ∃ y ∈ X.V ×ˢ X.V,
      Relation.ReflTransGen (Rises policy w ell) (a,b) y ∧ w y.1 ≠ w y.2 ∧
      (outN X.D X.V y.1).card ≠ (outN X.D X.V y.2).card ∧
      ∃ j, ((j ∈ exclusive X.D X.V y.1 y.2 \ (policy y.1 y.2).left ∧
               failsTransfer q X.D X.V π y.1 y.2 j) ∨
             (j ∈ exclusive X.D X.V y.2 y.1 \ (policy y.1 y.2).right ∧
               failsTransfer q X.D X.V π y.2 y.1 j)) ∧
        (j ∉ H ∨ (exclusive X.D X.V y.2 y.1).card < (exclusive X.D X.V y.1 y.2 ∩ H).card ∨
                 (exclusive X.D X.V y.1 y.2).card < (exclusive X.D X.V y.2 y.1 ∩ H).card) := by
  classical
  have pick (A B : Finset ℕ) : ∃ m : Matching A B,
      (A ∩ H).card ≤ B.card → (B ∩ H).card ≤ A.card → A ∩ H ⊆ m.left ∧ B ∩ H ⊆ m.right := by
    by_cases ok : (A ∩ H).card ≤ B.card ∧ (B ∩ H).card ≤ A.card
    · obtain ⟨m,cover⟩ := cover_labels (inter_subset_left : A ∩ H ⊆ A)
        (inter_subset_left : B ∩ H ⊆ B) ok.1 ok.2
      exact ⟨m,fun _ _ => cover⟩
    · exact ⟨chooseMatching A B,fun l r => (ok ⟨l,r⟩).elim⟩
  choose choosePair covers using pick
  let policy : Policy X.D X.V := fun a b => choosePair (exclusive X.D X.V a b) (exclusive X.D X.V b a)
  obtain ⟨y,yv,path,ne,deg,_,stop⟩ := marked_repair X hq small flat pos high cols divides policy av bv diff
  refine ⟨policy,y,yv,path,ne,deg,?_⟩
  obtain ⟨j,side⟩ : ∃ j, (j ∈ exclusive X.D X.V y.1 y.2 \ (policy y.1 y.2).left ∧
      failsTransfer q X.D X.V π y.1 y.2 j) ∨
      (j ∈ exclusive X.D X.V y.2 y.1 \ (policy y.1 y.2).right ∧
      failsTransfer q X.D X.V π y.2 y.1 j) := by
    rcases stop with ⟨j,m,f⟩ | ⟨j,m,f⟩
    · exact ⟨j,Or.inl ⟨m,f⟩⟩
    · exact ⟨j,Or.inr ⟨m,f⟩⟩
  refine ⟨j,side,?_⟩
  by_contra! bad
  have cover := covers _ _ bad.2.1 bad.2.2
  rcases side with ⟨m,_⟩ | ⟨m,_⟩
  · exact (mem_sdiff.mp m).2 (cover.1 (mem_inter.mpr ⟨(mem_sdiff.mp m).1,bad.1⟩))
  · exact (mem_sdiff.mp m).2 (cover.2 (mem_inter.mpr ⟨(mem_sdiff.mp m).1,bad.1⟩))

#print axioms has_exclusive
#print axioms cover_labels
#print axioms escape_label
#print axioms two_labels
#print axioms remembered_set

end LeanCH.BR.Closure.FeederPrivateHeadDescent
