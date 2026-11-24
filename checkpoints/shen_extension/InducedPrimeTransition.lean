import LeanCH.BR.BRSerialChain

/-! Same-cutoff descent on induced supports, with positive integer weights
and an upper bound on their total inherited from the input graph. -/
namespace LeanCH.BR.ShenPrimeTransition

open BRq2 BRq3 BR45 BRsub WeightedSD

def Strict (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℕ) : Prop :=
  ∀ i ∈ V, mass V (fun v => (w v : ℚ)) < row q D V (fun v => (w v : ℚ)) i

def Prime (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬(OutUniform D V M ∧ InUniform D V M)

/-- One fork for any substitution. Either an actual fiber inherits strictness
with unchanged weights, or the quotient inherits it with the integer fiber sums. -/
theorem strict_fork {q D E V I w} (P : Substitution D E V I) (h : Strict q D V w) :
    (∃ i ∈ I, Strict q D (P.fiber i) w) ∨
      Strict q E I (fun i => ∑ v ∈ P.fiber i, w v) := by
  classical
  by_cases inner : ∃ i ∈ I, Strict q D (P.fiber i) w
  · exact Or.inl inner
  right
  let wr := fun v => (w v : ℚ)
  have castMass (i) : (↑(∑ v ∈ P.fiber i, w v) : ℚ) = mass (P.fiber i) wr := by
    simp [mass, wr]
  intro i hi
  have fail : ¬ Strict q D (P.fiber i) w := fun yes => inner ⟨i,hi,yes⟩
  unfold Strict at fail
  push Not at fail
  obtain ⟨a,ha,low⟩ := fail
  have high := h a (P.fiber_subset hi ha)
  change mass V wr < row q D V wr a at high
  rw [P.mass_partition wr, P.row_partition q wr hi ha] at high
  simp only [castMass]
  change _ < mass (P.fiber i) wr + _
  exact high.trans_le (add_le_add low le_rfl)

/-- An induced prime witness of bounded mass on the original vertex labels. -/
structure Witness (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (budget : ℕ) where
  carrier : Finset ℕ
  subset : carrier ⊆ V
  nonempty : carrier.Nonempty
  prime : Prime D carrier
  weights : ℕ → ℕ
  positive : ∀ v ∈ carrier, 0 < weights v
  bounded : (∑ v ∈ carrier, weights v) ≤ budget
  strict : Strict q D carrier weights

private def Witness.extend {q D U V a b} (X : Witness q D U a)
    (sub : U ⊆ V) (le : a ≤ b) : Witness q D V b :=
  { X with subset := X.subset.trans sub, bounded := X.bounded.trans le }

theorem prime_descent {q D V w} (loop : ∀ v ∈ V, D v v = false)
    (ne : V.Nonempty) (pos : ∀ v ∈ V, 0 < w v) (h : Strict q D V w) :
    Nonempty (Witness q D V (∑ v ∈ V, w v)) := by
  classical
  by_cases done : Prime D V
  · exact ⟨⟨V,Finset.Subset.rfl,ne,done,w,pos,le_rfl,h⟩⟩
  unfold Prime at done
  push Not at done
  obtain ⟨M,sub,large,proper,hout,hin⟩ := done
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
  let P := moduleSubstitution sub hr hout hin loop
  let I := representativeSet V M r
  have isub : I ⊆ V := representative_subset sub hr
  have iprop : I ≠ V := representative_ne sub hr large
  have fiber_lt (i) (hi : i ∈ I) : (P.fiber i).card < V.card := by
    by_cases eq : i = r
    · subst i
      change (representativeFiber M r r).card < _
      simpa [representativeFiber] using
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,proper⟩)
    · have c := Finset.card_le_card sub
      change (representativeFiber M r i).card < _
      simp [representativeFiber,eq]
      omega
  rcases strict_fork P h with ⟨i,hi,hf⟩ | hq
  · have fs := P.fiber_subset hi
    obtain ⟨X⟩ := prime_descent (fun v hv => loop v (fs hv)) (P.nonempty i hi)
      (fun v hv => pos v (fs hv)) hf
    exact ⟨X.extend fs (Finset.sum_le_sum_of_subset_of_nonneg fs (by intros; omega))⟩
  · let t := fun i => ∑ v ∈ P.fiber i, w v
    have tpos (i) (hi : i ∈ I) : 0 < t i := by
      obtain ⟨a,ha⟩ := P.nonempty i hi
      exact (pos a (P.fiber_subset hi ha)).trans_le (Finset.single_le_sum (f:=w) (by intros; omega) ha)
    have massEq : ∑ i ∈ I, t i = ∑ v ∈ V, w v := by
      conv_rhs => rw [P.cover]
      exact (Finset.sum_biUnion P.disjoint).symm
    obtain ⟨X⟩ := prime_descent (fun v hv => loop v (isub hv))
      (show I.Nonempty from ⟨r,Finset.mem_insert_self _ _⟩) tpos hq
    exact ⟨X.extend isub massEq.le⟩
termination_by V.card
decreasing_by
  · exact fiber_lt i hi
  · exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨isub,iprop⟩)

theorem of_input {q n s D} (hn : 0<n) (order : n≤q*s) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n s) :
    Nonempty (Witness q D (Finset.range n) n) := by
  have h : Strict q D (Finset.range n) (fun _ => 1) := by
    intro v hv
    have hd : s ≤ (outN D (Finset.range n) v).card :=
      Compose.FloorSix.out_card degree (Finset.mem_range.mp hv)
    have hi : n < 1+q*(outN D (Finset.range n) v).card := by
      have := Nat.mul_le_mul_left q hd
      omega
    simp only [row,outW_unit,mass,Nat.cast_one,Finset.sum_const,Finset.card_range,
      nsmul_eq_mul,mul_one]
    exact_mod_cast hi
  simpa using prime_descent (fun v hv => loop v (Finset.mem_range.mp hv))
    (Finset.nonempty_range_iff.mpr (by omega : n≠0)) (fun _ _ => Nat.zero_lt_one) h

/-- All competing weights stay on induced subsets of the same input. -/
def Realized (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (b : ℕ) : Prop :=
  ∃ U ⊆ V, U.Nonempty ∧ ∃ w : ℕ → ℕ, (∀ v ∈ U, 0 < w v) ∧ Strict q D U w ∧
    (∑ v ∈ U, w v) = b

def Witness.Minimal {q D V b} (X : Witness q D V b) : Prop :=
  ∀ a, Realized q D V a → (∑ v ∈ X.carrier, X.weights v) ≤ a

theorem minimum_of_input {q n s D} (hn : 0<n) (order : n≤q*s) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n s) :
    ∃ X : Witness q D (Finset.range n) n, X.Minimal := by
  classical
  obtain ⟨A⟩ := of_input hn order loop degree
  let a := ∑ v ∈ A.carrier, A.weights v
  have start : Realized q D (Finset.range n) a :=
    ⟨A.carrier,A.subset,A.nonempty,A.weights,A.positive,A.strict,rfl⟩
  have ex : ∃ b, Realized q D (Finset.range n) b := ⟨a,start⟩
  obtain ⟨U,sub,ne,w,pos,h,total⟩ := Nat.find_spec ex
  obtain ⟨B⟩ := prime_descent (fun v hv => loop v (Finset.mem_range.mp (sub hv))) ne pos h
  have bound := total.le.trans ((Nat.find_min' ex start).trans A.bounded)
  exact ⟨B.extend sub bound,fun c hc => B.bounded.trans (total.le.trans (Nat.find_min' ex hc))⟩

def score (q : ℕ) (D : CH.Digraph) (U : Finset ℕ) (w : ℕ → ℕ) (i : ℕ) :=
  w i + q * ∑ v ∈ U, if D i v = true then w v else 0

theorem nat_strict {q D U w} : Strict q D U w ↔
    ∀ i ∈ U, (∑ v ∈ U, w v) < score q D U w i := by
  have eq (i) : ((score q D U w i : ℕ) : ℚ) = row q D U (fun v => (w v : ℚ)) i := by
    simp [score, row, outW, apply_ite (fun n : ℕ => (n : ℚ))]
  constructor <;> intro h i hi
  · have lt := h i hi
    rw [← eq] at lt
    simpa [mass, ← Nat.cast_sum] using lt
  · have lt := h i hi
    change _ < row _ _ _ _ _
    rw [← eq]
    simpa [mass, ← Nat.cast_sum] using (show ((∑ v ∈ U, w v : ℕ) : ℚ) < (score q D U w i : ℚ) by exact_mod_cast lt)

theorem light_after_edit {q D V b} {X : Witness q D V b} (least : X.Minimal)
    {U} (sub : U ⊆ V) (ne : U.Nonempty) (w : ℕ → ℕ) (pos : ∀ v ∈ U, 0 < w v)
    (less : (∑ v ∈ U, w v) < ∑ v ∈ X.carrier, X.weights v) :
    ∃ v ∈ U, score q D U w v ≤ ∑ i ∈ U, w i := by
  by_contra! fail
  exact less.not_ge (least _ ⟨U,sub,ne,w,pos,nat_strict.mpr fail,rfl⟩)

private theorem light_on_support {q D V b} {X : Witness q D V b} (least : X.Minimal)
    (w : ℕ → ℕ) (remains : ∃ i ∈ X.carrier, 0 < w i)
    (less : (∑ v ∈ X.carrier, w v) < ∑ v ∈ X.carrier, X.weights v) :
    ∃ v ∈ X.carrier, 0 < w v ∧ score q D X.carrier w v ≤ ∑ i ∈ X.carrier, w i := by
  classical
  let U := X.carrier.filter (fun i => 0 < w i)
  have sub : U ⊆ X.carrier := Finset.filter_subset _ _
  have zero (i) (hi : i ∈ X.carrier) (hu : i ∉ U) : w i = 0 := by
    by_contra! pos
    exact hu (Finset.mem_filter.mpr ⟨hi,by omega⟩)
  have total : (∑ i ∈ U, w i) = ∑ i ∈ X.carrier, w i := Finset.sum_subset sub zero
  obtain ⟨a,ha,pa⟩ := remains
  have ne : U.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨ha,pa⟩⟩
  obtain ⟨v,hv,light⟩ := light_after_edit least (sub.trans X.subset) ne w
    (fun _ hi => (Finset.mem_filter.mp hi).2) (total.trans_lt less)
  have rows : score q D U w v = score q D X.carrier w v := by
    unfold score
    rw [Finset.sum_subset sub (fun i hi hu => by simp [zero i hi hu])]
  exact ⟨v,sub hv,(Finset.mem_filter.mp hv).2,rows ▸ total ▸ light⟩

/-- The witness survives an arbitrary nonzero integer withdrawal on a
nonempty remaining support. Its debit pays its old margin plus the total
removed, even when entire vertices disappear. -/
theorem withdrawal_bill {q D V b} {X : Witness q D V b} (least : X.Minimal)
    (keep debit : ℕ → ℕ) (remains : ∃ i ∈ X.carrier, 0 < keep i)
    (split : ∀ i ∈ X.carrier, X.weights i = keep i + debit i)
    (removed : 0 < ∑ i ∈ X.carrier, debit i) :
    ∃ v ∈ X.carrier, 0 < keep v ∧ score q D X.carrier X.weights v + (∑ i ∈ X.carrier, debit i) ≤
      (∑ i ∈ X.carrier, X.weights i) + score q D X.carrier debit v := by
  classical
  have total : (∑ i ∈ X.carrier, X.weights i) =
      (∑ i ∈ X.carrier, keep i) + ∑ i ∈ X.carrier, debit i :=
    (Finset.sum_congr rfl split).trans Finset.sum_add_distrib
  obtain ⟨v,hv,pv,light⟩ := light_on_support least keep remains
    (by rw [total]; exact Nat.lt_add_of_pos_right removed)
  have inside : (∑ i ∈ X.carrier, if D v i = true then X.weights i else 0) =
      (∑ i ∈ X.carrier, if D v i = true then keep i else 0) +
      ∑ i ∈ X.carrier, if D v i = true then debit i else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => by by_cases h : D v i = true <;> simp [h,split i hi])
  have rowEq : score q D X.carrier X.weights v =
      score q D X.carrier keep v + score q D X.carrier debit v := by
    simp only [score, inside, split v hv, Nat.mul_add]
    omega
  exact ⟨v,hv,pv,by rw [rowEq,total]; omega⟩

/-- Every radix yields a coupled constraint on a single row: the quotient
weights have a light row among the labels with nonzero quotient, and the
remainders there must pay the entire original strict margin. -/
theorem remainder_row {q D V b} {X : Witness q D V b} (least : X.Minimal)
    {L : ℕ} (base : 2 ≤ L) (heavy : ∃ i ∈ X.carrier, L ≤ X.weights i) :
    let t := fun i => X.weights i / L
    let r := fun i => X.weights i % L
    ∃ v ∈ X.carrier, L ≤ X.weights v ∧
      score q D X.carrier t v ≤ (∑ i ∈ X.carrier, t i) ∧
      score q D X.carrier X.weights v + (∑ i ∈ X.carrier, r i) ≤
        (∑ i ∈ X.carrier, X.weights i) + score q D X.carrier r v := by
  classical
  dsimp only
  let t := fun i => X.weights i / L
  let r := fun i => X.weights i % L
  have split (i) : X.weights i = L*t i + r i := by
    dsimp [t,r]
    exact (Nat.mod_add_div (X.weights i) L).symm.trans (Nat.add_comm _ _)
  have total : (∑ i ∈ X.carrier, X.weights i) =
      L * (∑ i ∈ X.carrier, t i) + ∑ i ∈ X.carrier, r i := by
    calc
      _ = ∑ i ∈ X.carrier, (L*t i + r i) := Finset.sum_congr rfl (fun i _ => split i)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  obtain ⟨a,ha,pa⟩ := heavy
  have ta : 0 < t a := (Nat.div_pos pa (by omega))
  have tp : 0 < ∑ i ∈ X.carrier, t i :=
    ta.trans_le (Finset.single_le_sum (f:=t) (by intros; omega) ha)
  have less : (∑ i ∈ X.carrier, t i) < ∑ i ∈ X.carrier, X.weights i := by
    rw [total]
    have lo := Nat.mul_le_mul_right (∑ i ∈ X.carrier, t i) base
    omega
  obtain ⟨v,hv,pv,low⟩ := light_on_support least t ⟨a,ha,ta⟩ less
  have parent : L ≤ X.weights v := by
    by_contra! h
    exact (Nat.ne_of_gt pv) (Nat.div_eq_of_lt h)
  have inside : (∑ i ∈ X.carrier, if D v i = true then X.weights i else 0) =
      L*(∑ i ∈ X.carrier, if D v i = true then t i else 0) +
      ∑ i ∈ X.carrier, if D v i = true then r i else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by by_cases h : D v i = true <;> simp [h,split i])
  have rowEq : score q D X.carrier X.weights v =
      L * score q D X.carrier t v + score q D X.carrier r v := by
    simp only [score,inside,split v]
    ring
  refine ⟨v,hv,parent,low,?_⟩
  change score q D X.carrier X.weights v + (∑ i ∈ X.carrier, r i) ≤
    (∑ i ∈ X.carrier, X.weights i) + score q D X.carrier r v
  rw [rowEq,total]
  have bound := Nat.mul_le_mul_left L low
  omega

/-- Binary case in vertex labels, using actual heads of the same heavy row. -/
theorem odd_heads {q D V b} {X : Witness q D V b} (least : X.Minimal)
    (heavy : ∃ i ∈ X.carrier, 2 ≤ X.weights i) :
    let O := X.carrier.filter (fun i => X.weights i % 2 = 1)
    ∃ v ∈ X.carrier, 2 ≤ X.weights v ∧
      O.card < X.weights v % 2 + q * (outN D O v).card := by
  classical
  let O := X.carrier.filter (fun i => X.weights i % 2 = 1)
  obtain ⟨v,hv,pv,_,bill⟩ := remainder_row least (L:=2) (by decide) heavy
  have binary (i) : X.weights i % 2 = if X.weights i % 2 = 1 then 1 else 0 := by
    split <;> omega
  have total : (∑ i ∈ X.carrier, X.weights i % 2) = O.card := by
    simp only [O,Finset.card_filter]
    exact Finset.sum_congr rfl (fun i _ => binary i)
  have count : (∑ i ∈ X.carrier, if D v i = true then X.weights i % 2 else 0) =
      (outN D O v).card := by
    simp only [outN,O,Finset.card_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : X.weights i % 2 = 1
    · simp [h]
    · have zero : X.weights i % 2 = 0 := by omega
      simp [zero]
  change score q D X.carrier X.weights v + _ ≤ _ + (X.weights v % 2 + q * _) at bill
  dsimp only at bill
  rw [total,count] at bill
  have strict := nat_strict.mp X.strict v hv
  refine ⟨v,hv,pv,?_⟩
  change O.card < X.weights v % 2 + q * (outN D O v).card
  omega

private theorem score_add {q D U v} (hv : v ∈ U) {f a b : ℕ → ℕ}
    (eq : ∀ i ∈ U, f i = a i + b i) :
    score q D U f v = score q D U a v + score q D U b v := by
  have inside : (∑ i ∈ U, if D v i = true then f i else 0) =
      (∑ i ∈ U, if D v i = true then a i else 0) + ∑ i ∈ U, if D v i = true then b i else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => by by_cases e : D v i = true <;> simp [e,eq i hi])
  simp only [score, inside, eq v hv, Nat.mul_add]
  omega

/-- Every partition of the individual weight units into two nonempty colors
forces two distinct rows. Each is light on its own color; the other color
carries at least its full original strict surplus there. -/
theorem two_color_rows {q D V b} {X : Witness q D V b} (least : X.Minimal)
    (a c : ℕ → ℕ) (ha : ∃ i ∈ X.carrier, 0 < a i) (hc : ∃ i ∈ X.carrier, 0 < c i)
    (split : ∀ i ∈ X.carrier, X.weights i = a i + c i) :
    let T := ∑ i ∈ X.carrier, X.weights i
    let A := ∑ i ∈ X.carrier, a i
    let C := ∑ i ∈ X.carrier, c i
    ∃ u ∈ X.carrier, ∃ v ∈ X.carrier, u ≠ v ∧ 0 < a u ∧ 0 < c v ∧
      score q D X.carrier a u ≤ A ∧ score q D X.carrier c v ≤ C ∧
      score q D X.carrier X.weights u + C ≤ T + score q D X.carrier c u ∧
      score q D X.carrier X.weights v + A ≤ T + score q D X.carrier a v := by
  have total : (∑ i ∈ X.carrier, X.weights i) =
      (∑ i ∈ X.carrier, a i) + ∑ i ∈ X.carrier, c i :=
    (Finset.sum_congr rfl split).trans Finset.sum_add_distrib
  have pos (f : ℕ → ℕ) (hf : ∃ i ∈ X.carrier, 0 < f i) : 0 < ∑ i ∈ X.carrier, f i := by
    obtain ⟨i,hi,pi⟩ := hf
    exact pi.trans_le (Finset.single_le_sum (f:=f) (by intros; omega) hi)
  have pa := pos a ha
  have pc := pos c hc
  obtain ⟨u,hu,au,lowA⟩ := light_on_support least a ha (by rw [total]; omega)
  obtain ⟨v,hv,cv,lowC⟩ := light_on_support least c hc (by rw [total]; omega)
  have su := score_add (q:=q) (D:=D) hu split
  have sv := score_add (q:=q) (D:=D) hv split
  refine ⟨u,hu,v,hv,?_,au,cv,lowA,lowC,?_,?_⟩
  · rintro rfl
    have strict := nat_strict.mp X.strict u hu
    omega
  · omega
  · omega

/-- The two complementary roundings force opposite signs for the odd labels
on two distinct rows. Each sign pays the full margin on its own row. -/
theorem opposite_parity_rows {q D V b} {X : Witness q D V b} (least : X.Minimal)
    (heavy : ∃ i ∈ X.carrier, 2 ≤ X.weights i) :
    let r := fun i => X.weights i % 2
    let T := ∑ i ∈ X.carrier, X.weights i
    let R := ∑ i ∈ X.carrier, r i
    ∃ u ∈ X.carrier, ∃ v ∈ X.carrier, u ≠ v ∧ 2 ≤ X.weights u ∧
      score q D X.carrier X.weights u + R ≤ T + score q D X.carrier r u ∧
      score q D X.carrier X.weights v + score q D X.carrier r v ≤ T + R := by
  classical
  let t := fun i => X.weights i / 2
  let r := fun i => X.weights i % 2
  let c := fun i => t i + r i
  have split (i) : X.weights i = c i + t i := by dsimp [c,t,r]; omega
  have cs (i) : c i = t i + r i := rfl
  have sumSplit : (∑ i ∈ X.carrier, X.weights i) =
      (∑ i ∈ X.carrier, c i) + ∑ i ∈ X.carrier, t i :=
    (Finset.sum_congr rfl (fun i _ => split i)).trans Finset.sum_add_distrib
  have sumC : (∑ i ∈ X.carrier, c i) =
      (∑ i ∈ X.carrier, t i) + ∑ i ∈ X.carrier, r i := Finset.sum_add_distrib
  obtain ⟨a,ha,pa⟩ := heavy
  have pos : 0 < ∑ i ∈ X.carrier, t i :=
    (Nat.div_pos pa (by decide)).trans_le (Finset.single_le_sum (f:=t) (by intros; omega) ha)
  have pc : ∀ i ∈ X.carrier, 0 < c i := by
    intro i hi
    have := X.positive i hi
    dsimp [c,r,t]
    omega
  obtain ⟨v,hv,low⟩ := light_after_edit least X.subset X.nonempty c pc
    (by rw [sumSplit]; exact Nat.lt_add_of_pos_right pos)
  obtain ⟨u,hu,pu,_,high⟩ := remainder_row least (L:=2) (by decide) ⟨a,ha,pa⟩
  have sc := score_add (q:=q) (D:=D) hv (fun i _ => cs i)
  have sw := score_add (q:=q) (D:=D) hv (fun i _ => split i)
  have down : score q D X.carrier X.weights v + score q D X.carrier r v ≤
      (∑ i ∈ X.carrier, X.weights i) + ∑ i ∈ X.carrier, r i := by omega
  change score q D X.carrier X.weights u + (∑ i ∈ X.carrier, r i) ≤
    (∑ i ∈ X.carrier, X.weights i) + score q D X.carrier r u at high
  refine ⟨u,hu,v,hv,?_,pu,high,down⟩
  rintro rfl
  have strict := nat_strict.mp X.strict u hu
  omega

theorem prime_frontier {q n s D} (hq : 0<q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (no : ¬CH.HasDirectedCycleAtMost D n q) :
    ∃ X : Witness q D (Finset.range n) n,
      X.Minimal ∧ QFree D X.carrier q ∧ q+1 < X.carrier.card := by
  obtain ⟨X,least⟩ := minimum_of_input hn order loop degree
  have free := (qfree_of_noShort loop no).mono_set X.subset
  refine ⟨X,least,free,?_⟩
  by_contra! small
  have low := smallRow_of_card_le_succ hq free small
  exact low.no_strict X.nonempty _ (fun _ _ => Nat.cast_nonneg _) X.strict

/-- A structural branch for arbitrarily large inputs at every cutoff. -/
theorem cycle_of_small_prime {q n s D} (hq : 0<q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (small : ∀ U ⊆ Finset.range n, Prime D U → U.card ≤ q+1) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨X,_,_,large⟩ := prime_frontier hq hn order loop degree no
  exact large.not_ge (small _ X.subset X.prime)

#print axioms strict_fork
#print axioms prime_descent
#print axioms of_input
#print axioms minimum_of_input
#print axioms withdrawal_bill
#print axioms remainder_row
#print axioms odd_heads
#print axioms two_color_rows
#print axioms opposite_parity_rows
#print axioms prime_frontier
#print axioms cycle_of_small_prime
end LeanCH.BR.ShenPrimeTransition
