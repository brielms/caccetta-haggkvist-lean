import checkpoints.shen_extension.FeederPrivateHeadDescent
import checkpoints.shen_extension.EqualizerTransfer
import checkpoints.shen_extension.NativeReturnAccounts
import checkpoints.shen_extension.CrossValueOmissions

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent

open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier SharedArcBarrier

/-- A concrete withdrawal on the original reverse prices, evaluated at the label j. -/
def failsTransfer (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (π : ℕ → ℚ)
    (fromRow toRow j : ℕ) : Prop :=
  j ∈ V.erase fromRow ∧
    WeightedSD.col q D (V.erase fromRow) (transferWeight π fromRow toRow) j <
      mass (V.erase fromRow) (transferWeight π fromRow toRow)

theorem fails_iff_exclusive {q n} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) {π c} (pos : ∀ i ∈ X.V, 0 < π i)
    (high : mass X.V π < c) (flat : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {a b j} (av : a ∈ X.V) (bv : b ∈ X.V) (ne : a ≠ b) :
    failsTransfer q X.D X.V π a b j ↔ j ∈ exclusive X.D X.V a b := by
  classical
  have test (jv : j ∈ X.V.erase a) :=
    (EqualizerTransfer.classify hq X.free.reverse small (fun i hi => (pos i hi).le)
      high flat av bv ne jv).1
  constructor
  · rintro ⟨jv,low⟩
    obtain ⟨aj,bj⟩ := (test jv).mp low
    exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨mem_of_mem_erase jv,aj⟩,
      fun h => Bool.noConfusion (bj.symm.trans (mem_outN.mp h).2)⟩
  · intro ex
    obtain ⟨aj,miss⟩ := mem_sdiff.mp ex
    obtain ⟨jv,edge⟩ := mem_outN.mp aj
    have ja : j ≠ a := fun eq => loopfree X.free (by omega) av (eq ▸ edge)
    have bj : X.D b j = false := Bool.eq_false_iff.mpr (fun t => miss (mem_outN.mpr ⟨jv,t⟩))
    exact ⟨mem_erase.mpr ⟨ja,jv⟩,(test (mem_erase.mpr ⟨ja,jv⟩)).mpr ⟨edge,bj⟩⟩

/-- The ordinary rational deficit over any chosen part of the one-sided bank.
Only the receiving row itself gets a diagonal rebate. -/
theorem exact_bill {D V q π c a b} (av : a ∈ V) (bv : b ∈ V) (ne : a ≠ b)
    (cols : ∀ j ∈ V, WeightedSD.col q D V π j = c)
    {T : Finset ℕ} (aff : T ⊆ exclusive D V a b) :
    (∑ j ∈ T, (mass (V.erase a) (transferWeight π a b) -
      WeightedSD.col q D (V.erase a) (transferWeight π a b) j)) =
    (T.card : ℚ) * ((q : ℚ) * π a - (c - mass V π)) -
      (if b ∈ T then π a else 0) := by
  classical
  have point j (hj : j ∈ T) :
      mass (V.erase a) (transferWeight π a b) -
        WeightedSD.col q D (V.erase a) (transferWeight π a b) j =
      ((q : ℚ) * π a - (c - mass V π)) - (if j = b then π a else 0) := by
    obtain ⟨aj,no⟩ := mem_sdiff.mp (aff hj)
    obtain ⟨jv,ed⟩ := mem_outN.mp aj
    have miss : D b j = false := Bool.eq_false_iff.mpr (fun e => no (mem_outN.mpr ⟨jv,e⟩))
    have old := cols j jv
    unfold WeightedSD.col at old
    rw [mass_transfer av bv ne]
    change mass V π - WeightedSD.row q (fun i k => D k i) (V.erase a) _ j = _
    rw [WeightedSD.row,outW_transfer (mem_erase.mpr ⟨ne.symm,bv⟩)]
    change mass V π - (transferWeight π a b j + (q : ℚ) *
      (inW D (V.erase a) π j + (if D b j = true then π a else 0))) = _
    rw [inW_erase av,ed] at old
    rw [miss]
    unfold transferWeight
    split_ifs <;> simp_all <;> linarith
  rw [sum_congr rfl point,sum_sub_distrib]
  simp
  ring

/-- Same receivers, graph, and prices across the trace. At the end one direction
has more strictly unpaid columns, and its unmatched bank contains an actual such
column even after every possible opposing head has been paired. -/
theorem marked_repair {q n} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) {w π c} (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {ell : ℕ} [Fact ell.Prime] (divides : ell ∣ q) (policy : Policy X.D X.V)
    {a b} (av : a ∈ X.V) (bv : b ∈ X.V) (diff : w a ≠ w b) :
    ∃ y ∈ X.V ×ˢ X.V, Relation.ReflTransGen (Rises policy w ell) (a,b) y ∧
      w y.1 ≠ w y.2 ∧ (outN X.D X.V y.1).card ≠ (outN X.D X.V y.2).card ∧
      padicNorm ell (gap w y) < padicNorm ell (remainder (policy y.1 y.2) w) ∧
      ((∃ j ∈ exclusive X.D X.V y.1 y.2 \ (policy y.1 y.2).left,
           failsTransfer q X.D X.V π y.1 y.2 j) ∨
       (∃ j ∈ exclusive X.D X.V y.2 y.1 \ (policy y.1 y.2).right,
           failsTransfer q X.D X.V π y.2 y.1 j)) := by
  classical
  obtain ⟨y,yv,path,ne,deg,rise⟩ := trace_to_bank divides flat policy av bv diff
  obtain ⟨yv₁,yv₂⟩ := mem_product.mp yv
  have sep : y.1 ≠ y.2 := fun e => ne (congrArg w e)
  refine ⟨y,yv,path,ne,deg,rise,?_⟩
  by_cases l : (exclusive X.D X.V y.1 y.2 \ (policy y.1 y.2).left).Nonempty
  · obtain ⟨j,jl⟩ := l
    exact Or.inl ⟨j,jl,(fails_iff_exclusive X hq small pos high cols yv₁ yv₂ sep).mpr (mem_sdiff.mp jl).1⟩
  by_cases r : (exclusive X.D X.V y.2 y.1 \ (policy y.1 y.2).right).Nonempty
  · obtain ⟨j,jr⟩ := r
    exact Or.inr ⟨j,jr,(fails_iff_exclusive X hq small pos high cols yv₂ yv₁ sep.symm).mpr (mem_sdiff.mp jr).1⟩
  rw [not_nonempty_iff_eq_empty] at l r
  have zero : remainder (policy y.1 y.2) w = 0 := by simp [remainder,l,r,mass]
  rw [zero,padicNorm.zero] at rise
  exact (not_lt_of_ge (padicNorm.nonneg _) rise).elim

/-- Applies directly to the two named feeders in the capstone. When their original
prices agree the first alternative records this explicitly. The shared receiver is
cancelled in both directions. -/
theorem at_boundary_feeders {q n} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) {w π c} (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {F L a b z} (boundary : Boundary X F L) (al : a ∈ L) (bl : b ∈ L)
    (az : graph X.D F a z = true) (bz : graph X.D F b z = true) :
    z ∉ exclusive X.D X.V a b ∧ z ∉ exclusive X.D X.V b a ∧
      (w a = w b ∨ ∀ (ell : ℕ) [Fact ell.Prime], ell ∣ q → ∀ policy : Policy X.D X.V,
        ∃ y ∈ X.V ×ˢ X.V, Relation.ReflTransGen (Rises policy w ell) (a,b) y ∧
          w y.1 ≠ w y.2 ∧ (outN X.D X.V y.1).card ≠ (outN X.D X.V y.2).card ∧
          padicNorm ell (gap w y) < padicNorm ell (remainder (policy y.1 y.2) w) ∧
          ((∃ j ∈ exclusive X.D X.V y.1 y.2 \ (policy y.1 y.2).left,
                failsTransfer q X.D X.V π y.1 y.2 j) ∨
           (∃ j ∈ exclusive X.D X.V y.2 y.1 \ (policy y.1 y.2).right,
                failsTransfer q X.D X.V π y.2 y.1 j))) := by
  classical
  have cl : Cycle X.D X.V q L := (mem_filter.mp boundary.1).2
  have ea := CrossValueOmissions.selected_sub az
  have eb := CrossValueOmissions.selected_sub bz
  refine ⟨fun h => (mem_sdiff.mp h).2 (mem_outN.mpr ⟨(mem_outN.mp (mem_sdiff.mp h).1).1,eb⟩),
    fun h => (mem_sdiff.mp h).2 (mem_outN.mpr ⟨(mem_outN.mp (mem_sdiff.mp h).1).1,ea⟩),?_⟩
  by_cases same : w a = w b
  · exact Or.inl same
  exact Or.inr (fun _ _ d policy => marked_repair X hq small flat pos high cols d policy (cl.sub al) (cl.sub bl) same)

#print axioms fails_iff_exclusive
#print axioms exact_bill
#print axioms marked_repair
#print axioms at_boundary_feeders

end LeanCH.BR.Closure.FeederPrivateHeadDescent
