import LeanCH.BR.BRWeightedSmallRow
import LeanCH.BR.BRNearBoundaryRows
import LeanCH.BR.BRWeightedCritical

/-! Substitution, actual module contraction, and return geometry for the
strict branch using only smaller-instance small-row hypotheses. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem Substitution.smallRow {q : ℕ} {D E : CH.Digraph} {V I : Finset ℕ}
    (P : Substitution D E V I) (hquot : SmallRow q E I)
    (hinside : ∀ i ∈ I, SmallRow q D (P.fiber i)) : SmallRow q D V := by
  intro w hw hV
  let t := fun i => mass (P.fiber i) w
  have hsub : ∀ i ∈ I, ∀ a ∈ P.fiber i, 0 ≤ w a :=
    fun i hi a ha => hw a (P.fiber_subset hi ha)
  have ht : ∀ i ∈ I, 0 ≤ t i := fun i hi => mass_nonneg (hsub i hi)
  have hI : I.Nonempty := by
    obtain ⟨a, ha⟩ := hV
    obtain ⟨i, hi, _⟩ := Finset.mem_biUnion.mp (P.cover ▸ ha)
    exact ⟨i, hi⟩
  obtain ⟨i, hi, hsmall⟩ := hquot t ht hI
  obtain ⟨a, ha, hinner⟩ := hinside i hi w (hsub i hi) (P.nonempty i hi)
  refine ⟨a, P.fiber_subset hi ha, ?_⟩
  rw [P.row_partition q w hi ha, P.mass_partition w]
  change _ ≤ mass I t
  have hh : row q D (P.fiber i) w a + q * outW E I t i ≤ row q E I t i := by
    change _ ≤ mass (P.fiber i) w + q * outW E I t i
    linarith
  exact hh.trans hsmall

theorem smallRow_of_proper_module {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U)
    (hMV : M ⊆ V) (hM : 2 ≤ M.card) (hne : M ≠ V) (hout : OutUniform D V M) :
    SmallRow q D V := by
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
  have hin := outUniform_inUniform hf hsat hMV hout
  let P := moduleSubstitution hMV hr hout hin
    (fun v hv => Bool.eq_false_iff.mpr (loopfree hf hq hv))
  apply P.smallRow
  · exact hproper _ (representative_subset hMV hr) (representative_ne hMV hr hM)
  · intro i hi
    by_cases hir : i = r
    · subst i
      simpa [P, moduleSubstitution, representativeFiber] using hproper M hMV hne
    · have hiV : i ∈ V := (representative_outside hi hir).1
      have hsing : ({i} : Finset ℕ) ≠ V := by
        intro he
        have hc := Finset.card_le_card hMV
        rw [← he] at hc
        simp only [Finset.card_singleton] at hc
        omega
      simpa [P, moduleSubstitution, representativeFiber, hir] using
        hproper {i} (Finset.singleton_subset_iff.mpr hiV) hsing

theorem smallRow_of_supergraph {q : ℕ} {D E : CH.Digraph} {V : Finset ℕ}
    (hDE : ∀ a ∈ V, ∀ b ∈ V, D a b = true → E a b = true)
    (hE : SmallRow q E V) : SmallRow q D V := by
  intro w hw hV
  obtain ⟨v, hv, hs⟩ := hE w hw hV
  refine ⟨v, hv, le_trans ?_ hs⟩
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (outW_mono_graph hDE hw hv) (Nat.cast_nonneg q))

/-- The induction class includes every q-free graph of smaller order,
not just induced subsets of one selected graph. -/
def SmallerSmallRow (q n : ℕ) : Prop :=
  ∀ (D : CH.Digraph) (V : Finset ℕ), V.card < n → QFree D V q → SmallRow q D V

theorem SmallerSmallRow.induced {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : SmallerSmallRow q V.card) (hf : QFree D V q) :
    ∀ U ⊆ V, U ≠ V → SmallRow q D U := by
  intro U hUV hne
  exact h D U (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hUV, hne⟩))
    (hf.mono_set hUV)

theorem SmallerSmallRow.reverse_induced {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : SmallerSmallRow q V.card) (hf : QFree D V q) :
    ∀ U ⊆ V, U ≠ V → SmallRow q (fun a b => D b a) U :=
  h.induced hf.reverse

theorem strict_no_incoming_domination {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v)
    {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) (hne : x ≠ y)
    (hdom : ∀ v ∈ V.erase x, D v x = true → D v y = true) : False := by
  let K := V.erase x
  let z := transferWeight w x y
  have hKV : K ⊆ V := Finset.erase_subset _ _
  have hyK : y ∈ K := Finset.mem_erase.mpr ⟨hne.symm, hy⟩
  have hneK : K ≠ V := by
    intro he
    have hh : x ∈ K := by rw [he]; exact hx
    exact Finset.notMem_erase x V hh
  have hwz : ∀ v ∈ K, 0 ≤ z v := by
    intro v hv
    dsimp [z, transferWeight]
    split_ifs <;> linarith [hw v (hKV hv), hw x hx]
  have hm : mass K z = mass V w := mass_transfer hx hy hne w
  have hout : ∀ v ∈ K, outW D V w v ≤ outW D K z v := by
    intro v hv
    rw [outW_erase hx w v, outW_transfer hyK]
    by_cases hdx : D v x = true
    · simp [K, hdx, hdom v hv hdx]
    · by_cases hdy : D v y = true <;> simp [K, hdx, hdy, hw x hx]
  apply (hproper K hKV hneK).no_strict ⟨y, hyK⟩ z hwz
  intro v hv
  rw [hm]
  apply (hr v (hKV hv)).trans_le
  apply add_le_add
  · dsimp [z, transferWeight]
    split_ifs <;> linarith [hw x hx]
  · exact mul_le_mul_of_nonneg_left (hout v hv) (Nat.cast_nonneg q)

theorem strict_no_outgoing_domination {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v)
    (hc : ∀ v ∈ V, mass V p < col q D V p v)
    {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) (hne : x ≠ y)
    (hdom : ∀ v ∈ V.erase x, D x v = true → D y v = true) : False :=
  strict_no_incoming_domination (hsmall.reverse_induced hf) p hp hc hx hy hne hdom

theorem arc_return_exact_of_smallRow {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v)
    {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) (hxy : D x y = true) : Walk D V y x q := by
  have hne : x ≠ y := by
    intro he
    subst y
    exact loopfree hf hq hx hxy
  have hreach : x ∈ ball D V y q := by
    by_contra hn
    apply strict_no_incoming_domination hproper w hw hr hx hy hne
    intro v hv hvx
    by_contra hvy
    have hball := hsat y hy v (Finset.mem_erase.mp hv).2 hvy
    exact hn (ball_mono_radius (by omega) (ball_step hball hx hvx))
  obtain ⟨_, k, hk, hwalk⟩ := mem_ball.mp hreach
  have hkeq : k = q := by
    by_contra hn
    exact hf x (k + 1) (by omega) (by omega) (.step hy hxy hwalk)
  simpa only [hkeq] using hwalk

theorem diameter_le_of_smallRow {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SmallRow q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v)
    {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) : y ∈ ball D V x q := by
  by_cases hyx : D y x = true
  · exact mem_ball.mpr ⟨hy, q, le_rfl,
      arc_return_exact_of_smallRow hq hf hsat hproper w hw hr hy hx hyx⟩
  · exact ball_mono_radius (by omega) (hsat x hx y hy hyx)

theorem reverse_strict_of_pair {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {p : ℕ → ℚ} {c : ℚ} (hc : 1 < c) (hp : ∀ v ∈ V, 0 < p v)
    (hm : mass V p = 1) (hcol : ∀ v ∈ V, col q D V p v = c) :
    StrictPositiveRows q (fun a b => D b a) V := by
  refine ⟨p, hp, hm, ?_⟩
  intro v hv
  change 1 < col q D V p v
  rw [hcol v hv]
  exact hc

theorem realMatrix_reverse (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) :
    realMatrix q (fun a b => D b a) V = (realMatrix q D V).transpose := by
  ext i j
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    by_cases he : D j i = true <;>
      simp [realMatrix, WeightedArithmetic.rationalMatrix, WeightedArithmetic.closedMatrix,
        adjacencyMatrix, Matrix.transpose_apply, Matrix.one_apply, hij, hji, he]

theorem commonInverse_reverse {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (hH : FiniteCutInverse.CommonInverse (realMatrix q D V) H) :
    FiniteCutInverse.CommonInverse (realMatrix q (fun a b => D b a) V) H.transpose := by
  constructor
  · intro i j
    exact hH.nonneg j i
  · have hl : H * FiniteCutInverse.excess (realMatrix q D V) = 1 :=
      mul_eq_one_comm.mp hH.right
    have he : FiniteCutInverse.excess (realMatrix q (fun a b => D b a) V) =
        (FiniteCutInverse.excess (realMatrix q D V)).transpose := by
      rw [realMatrix_reverse]
      rfl
    rw [he, ← Matrix.transpose_mul, hl, Matrix.transpose_one]

/-- Smaller-order weighted induction supplies certificates in both
orientations. Their constraints use H and its transpose, not unrelated
inverse choices or an assumed equality of the two weightings. -/
theorem two_sided_cut_certificates_of_smaller {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v) :
    ∃ H : Matrix V V ℝ, FiniteCutInverse.CommonInverse (realMatrix q D V) H ∧
      FiniteCutInverse.CommonInverse (realMatrix q (fun a b => D b a) V) H.transpose ∧
      ∀ M ⊆ V, M.Nonempty → M ≠ V →
        (∃ r : V → ℝ, FiniteCutInverse.CutCertificate (realMatrix q D V) (hostCut V M) r) ∧
        (∃ p : V → ℝ, FiniteCutInverse.CutCertificate
          (realMatrix q (fun a b => D b a) V) (hostCut V M) p) := by
  obtain ⟨H, hH, hcuts⟩ := all_cut_certificates_of_proper_smallRow (hsmall.induced hf) w hw hr
  refine ⟨H, hH, commonInverse_reverse hH, ?_⟩
  intro M hMV hM hne
  refine ⟨hcuts M hMV hM hne, ?_⟩
  obtain ⟨p, hp⟩ := realDual_of_smallRow (hsmall.reverse_induced hf M hMV hne) hM
  exact ⟨_, cutCertificate_of_realDual hMV hp⟩

end LeanCH.BR.WeightedSD
