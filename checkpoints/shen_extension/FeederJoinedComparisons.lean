import checkpoints.shen_extension.FeederCycleSpill

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent
open Finset Function BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights

/-- A derivation from one marked pair. Joining two comparisons is allowed only
at a common physical label. Descending chooses one private head from each row. -/
inductive Joined (D : CH.Digraph) (V : Finset ℕ) (a b : ℕ) : ℕ → ℕ → Prop
  | seed : Joined D V a b a b
  | refl (x : ℕ) : Joined D V a b x x
  | symm {x y} : Joined D V a b x y → Joined D V a b y x
  | trans {x y z} : Joined D V a b x y → Joined D V a b y z → Joined D V a b x z
  | heads {x y i j} : Joined D V a b x y → i ∈ exclusive D V x y → j ∈ exclusive D V y x →
      Joined D V a b i j

theorem joined_of_compared {D V a b y} (p : Compared D V (a,b) y) : Joined D V a b y.1 y.2 := by
  induction p with
  | refl => exact .seed
  | tail _ step ih => exact ih.heads step.1 step.2

private theorem banks_join {D V a b x y}
    (sep : ∀ u ∈ V, ∀ v ∈ V, u ≠ v → (exclusive D V u v).Nonempty)
    (xv : x ∈ V) (yv : y ∈ V) (ne : x ≠ y) (xy : Joined D V a b x y)
    {i j} (ih : i ∈ exclusive D V x y ∪ exclusive D V y x)
    (jh : j ∈ exclusive D V x y ∪ exclusive D V y x) : Joined D V a b i j := by
  obtain ⟨u,hu⟩ := sep x xv y yv ne
  obtain ⟨v,hv⟩ := sep y yv x xv ne.symm
  have toV (k) (hk : k ∈ exclusive D V x y ∪ exclusive D V y x) : Joined D V a b k v := by
    rcases mem_union.mp hk with left | right
    · exact xy.heads left hv
    · exact (xy.heads hu right).symm.trans (xy.heads hu hv)
  exact (toV i ih).trans (toV j jh).symm

/-- A proper comparison class containing an arc would be an outgoing module.
The statement applies equally to a strict attachment which has not been saturated. -/
theorem comparison_class_spans {D V a b r x k}
    (loops : ∀ i ∈ V, D i i ≠ true)
    (sep : ∀ u ∈ V, ∀ v ∈ V, u ≠ v → (exclusive D V u v).Nonempty)
    (prime : ∀ C ⊆ V, 2 ≤ C.card → C ≠ V → ¬ BRsub.OutUniform D V C)
    (xv : x ∈ V) (kv : k ∈ V)
    (rx : Joined D V a b r x) (rk : Joined D V a b r k) (arc : D x k = true) :
    ∀ t ∈ V, Joined D V a b r t := by
  classical
  let C := V.filter (Joined D V a b r)
  have xc : x ∈ C := mem_filter.mpr ⟨xv,rx⟩
  have kc : k ∈ C := mem_filter.mpr ⟨kv,rk⟩
  have sub : C ⊆ V := filter_subset _ _
  have loop := loops k kv
  have apart : x ≠ k := by rintro rfl; exact loop arc
  have matchOutside {u v z} (uc : u ∈ C) (vc : v ∈ C) (hit : D u k = true)
      (miss : D v k ≠ true) (zv : z ∈ V) (outside : z ∉ C) : D u z = D v z := by
    have uv : Joined D V a b u v := (mem_filter.mp uc).2.symm.trans (mem_filter.mp vc).2
    have neq : u ≠ v := by rintro rfl; exact miss hit
    have priv : k ∈ exclusive D V u v :=
      mem_sdiff.mpr ⟨mem_outN.mpr ⟨kv,hit⟩,fun h => miss (mem_outN.mp h).2⟩
    have blocked (h : z ∈ exclusive D V u v ∪ exclusive D V v u) : False := by
      have kz := banks_join sep (sub uc) (sub vc) neq uv (mem_union_left _ priv) h
      exact outside (mem_filter.mpr ⟨zv,rk.trans kz⟩)
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro uz
      by_contra vz
      exact blocked (mem_union_left _ (mem_sdiff.mpr ⟨mem_outN.mpr ⟨zv,uz⟩,fun h => vz (mem_outN.mp h).2⟩))
    · intro vz
      by_contra uz
      exact blocked (mem_union_right _ (mem_sdiff.mpr ⟨mem_outN.mpr ⟨zv,vz⟩,fun h => uz (mem_outN.mp h).2⟩))
  have full : C = V := by
    by_contra proper
    have out : BRsub.OutUniform D V C := by
      intro i ic j jc z zv outside
      have anchor (u) (uc : u ∈ C) : D u z = D x z := by
        by_cases uk : D u k = true
        · exact (matchOutside uc kc uk loop zv outside).trans (matchOutside xc kc arc loop zv outside).symm
        · exact (matchOutside xc uc arc uk zv outside).symm
      exact (anchor i ic).trans (anchor j jc).symm
    exact prime C sub (one_lt_card.mpr ⟨x,xc,k,kc,apart⟩) proper out
  intro t tv
  exact (mem_filter.mp (show t ∈ C from full ▸ tv)).2

/-- In the native model, saturation and primeness supply the outgoing-module test. -/
theorem joined_arc_spans {q n a b r x k} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) {π c}
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    (xv : x ∈ X.V) (kv : k ∈ X.V)
    (rx : Joined X.D X.V a b r x) (rk : Joined X.D X.V a b r k) (arc : X.D x k = true) :
    ∀ t ∈ X.V, Joined X.D X.V a b r t := by
  apply comparison_class_spans (fun _ hi => loopfree X.free (by omega : 1 ≤ q) hi)
    (fun _ hu _ hv => has_exclusive X hq small pos high cols hu hv)
    (fun C sub two proper out =>
      X.prime C sub two proper ⟨out,BRsub.outUniform_inUniform X.free X.sat sub out⟩)
    xv kv rx rk arc

/-- Rotating and then joining the two marked rows covers every label of a
shortest cycle when their spacing is coprime to its length. -/
theorem cycle_join {D V q L a b} (hq : 1 ≤ q) (free : QFree D V q)
    (cy : Cycle D V q L) (ha : a ∈ L) (hb : b ∈ L) (ne : a ≠ b)
    (cop : Nat.Coprime (MandatoryExcursion.span D V q a b) (q+1)) :
    ∀ x ∈ L, Joined D V a b a x := by
  classical
  let s := fun i => (nextOn D L)^[i] a
  let k := MandatoryExcursion.span D V q a b
  obtain ⟨_,period,onto,_⟩ := cycle_index hq free cy ha
  change ∀ i, s (i+(q+1)) = s i at period
  change (range (q+1)).image s = L at onto
  have endAt : s k = b := by
    have seg := (MandatoryExcursion.segments hq free cy ha hb).2.2.1
    exact walk_next cy ha seg
  let linked (i : ℕ) := Joined D V a b a (s i)
  have left (i) : linked (i+k) = linked i := by
    have rot := joined_of_compared (cycle_rotations cy ha hb ne i)
    have atRight : s (i+k) = (nextOn D L)^[i] b := by
      change (nextOn D L)^[i+k] a = _
      rw [iterate_add_apply,show (nextOn D L)^[k] a=b from endAt]
    change Joined D V a b (s i) ((nextOn D L)^[i] b) at rot
    rw [←atRight] at rot
    exact propext ⟨fun h => h.trans rot.symm,fun h => h.trans rot⟩
  have right (i) : linked (i+(q+1)) = linked i := congrArg (Joined D V a b a) (period i)
  have unit := period_gcd left right
  change k.gcd (q+1) = 1 at cop
  rw [cop] at unit
  have all (i) : linked i := by
    induction i with
    | zero => exact .refl _
    | succ i ih => exact (unit i).symm ▸ ih
  intro x hx
  rw [←onto] at hx
  obtain ⟨i,_,rfl⟩ := mem_image.mp hx
  exact all i

/-- Once one class spans, every variation in native price or degree is
accessible by these rules. Global regularity is the remaining flat alternative. -/
theorem joined_or_regular {q n a b} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) {w π c}
    (posw : ∀ i ∈ X.V, 0 < w i) (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    (full : ∀ i ∈ X.V, Joined X.D X.V a b a i) :
    (∃ i ∈ X.V, ∃ j ∈ X.V, Joined X.D X.V a b i j ∧ w i ≠ w j ∧
      ∀ ell, ell.Prime → ell ∣ q → SignatureExit X w π c i j ell) ∨
    (∀ i ∈ X.V, ∀ j ∈ X.V, w i = w j ∧ (outN X.D X.V i).card = (outN X.D X.V j).card) := by
  classical
  by_cases any : ∃ i ∈ X.V, ∃ j ∈ X.V, w i ≠ w j
  · obtain ⟨i,iv,j,jv,neq⟩ := any
    refine Or.inl ⟨i,iv,j,jv,(full i iv).symm.trans (full j jv),neq,?_⟩
    intro ell prime dv
    let _ : Fact ell.Prime := ⟨prime⟩
    rcases comparison_fork X hq small dv posw flat pos high cols iv jv (fun e => neq (congrArg w e)) with win | tied
    · exact win
    exact (neq (tied _ .refl).1).elim
  · push Not at any
    right
    intro i iv j jv
    refine ⟨any i iv j jv,?_⟩
    have constant (u) (uv : u ∈ X.V) :
        mass (outN X.D X.V u) w = ((outN X.D X.V u).card : ℚ)*w i := by
      unfold mass
      calc
        _ = ∑ _ ∈ outN X.D X.V u, w i := sum_congr rfl (fun v hv => any v (mem_outN.mp hv).1 i iv)
        _ = _ := by simp
    have A := flat i iv
    have B := flat j jv
    rw [WeightedSD.row,outW_eq_mass,constant i iv] at A
    rw [WeightedSD.row,outW_eq_mass,constant j jv,any j jv i iv] at B
    have qp : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
    have eq : ((outN X.D X.V i).card : ℚ) = (outN X.D X.V j).card := by
      have h := (mul_left_cancel₀ qp.ne' (add_left_cancel (A.trans B.symm)))
      exact mul_right_cancel₀ (posw i iv).ne' h
    exact_mod_cast eq

theorem marked_spans {q n L a b} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {π c} (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    (cy : Cycle X.D X.V q L) (ha : a ∈ L) (hb : b ∈ L) (ne : a ≠ b)
    (cop : Nat.Coprime (MandatoryExcursion.span X.D X.V q a b) (q+1)) :
    ∀ t ∈ X.V, Joined X.D X.V a b a t := by
  obtain ⟨u,hu⟩ := card_pos.mp (show 0 < (outN X.D L a).card by rw [cy.heads a ha]; decide)
  obtain ⟨ul,au⟩ := mem_outN.mp hu
  exact joined_arc_spans X hq small pos high cols (cy.sub ha) (cy.sub ul) (.refl _)
    (cycle_join (by omega) X.free cy ha hb ne cop u ul) au

#print axioms comparison_class_spans
#print axioms joined_of_compared
#print axioms joined_arc_spans
#print axioms cycle_join
#print axioms joined_or_regular
#print axioms marked_spans
end LeanCH.BR.Closure.FeederPrivateHeadDescent
