/-
  Information theory on words: the independence bound.

  `H(Y_1,\dots,Y_n) \le \sum_i H(Y_i)` for any law on words of length `n`.

  The proof is an induction that peels the last coordinate off a word,
  turning a law on `Fin (n+1) → β` into a two-variable joint law on
  (prefix, last symbol).  That reduces each step to the ordinary two-variable
  subadditivity already proved, so no conditional mutual information and no
  `n`-fold chain rule are required.
-/

import Development.FiniteInformation

set_option autoImplicit false

open scoped BigOperators

namespace TranscendenceTower.FiniteInformation

noncomputable section

variable {β : Type} [Fintype β] [DecidableEq β]

/-! ## Peeling the last coordinate -/

/-- Words of length `n+1` are prefixes of length `n` paired with a last
symbol. -/
def snocEquiv (n : ℕ) : ((Fin n → β) × β) ≃ (Fin (n + 1) → β) where
  toFun p := Fin.snoc p.1 p.2
  invFun w := (Fin.init w, w (Fin.last n))
  left_inv p := by simp
  right_inv w := by simp

/-- A sum over words of length `n+1` splits as a sum over prefixes and last
symbols. -/
theorem sum_snoc {n : ℕ} (f : (Fin (n + 1) → β) → ℝ) :
    ∑ w : Fin (n + 1) → β, f w
      = ∑ w : Fin n → β, ∑ b : β, f (Fin.snoc w b) := by
  have h : ∑ p : (Fin n → β) × β, f (Fin.snoc p.1 p.2)
      = ∑ w : Fin (n + 1) → β, f w :=
    Fintype.sum_equiv (snocEquiv n) _ _ (fun _ => rfl)
  rw [← h, Fintype.sum_prod_type]

/-- A law on words of length `n+1`, read as a joint law on
(prefix, last symbol). -/
def splitLast {n : ℕ} (law : (Fin (n + 1) → β) → ℝ) : (Fin n → β) → β → ℝ :=
  fun w b => law (Fin.snoc w b)

/-- The `i`-th coordinate marginal of a law on words. -/
def coordMarginal {n : ℕ} (law : (Fin n → β) → ℝ) (i : Fin n) : β → ℝ :=
  fun b => ∑ w : Fin n → β, if w i = b then law w else 0

/-! ## Identifying the marginals of the split -/

/-- The last-symbol marginal of the split is the last coordinate marginal. -/
theorem sndMarginal_splitLast {n : ℕ} (law : (Fin (n + 1) → β) → ℝ) :
    sndMarginal (splitLast law) = coordMarginal law (Fin.last n) := by
  funext b
  unfold sndMarginal coordMarginal splitLast
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Fin.snoc_last]

/-- Marginalizing out the last symbol commutes with taking an earlier
coordinate marginal. -/
theorem coordMarginal_fstMarginal_splitLast {n : ℕ}
    (law : (Fin (n + 1) → β) → ℝ) (i : Fin n) :
    coordMarginal (fstMarginal (splitLast law)) i
      = coordMarginal law i.castSucc := by
  funext b
  unfold coordMarginal fstMarginal splitLast
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : w i = b
  · simp [h]
  · simp [h]

/-! ## Nonnegativity and normalization pass to the split -/

theorem splitLast_nonneg {n : ℕ} {law : (Fin (n + 1) → β) → ℝ}
    (hnn : ∀ w, 0 ≤ law w) (w : Fin n → β) (b : β) : 0 ≤ splitLast law w b :=
  hnn _

theorem splitLast_sum {n : ℕ} {law : (Fin (n + 1) → β) → ℝ}
    (hsum : ∑ w, law w = 1) :
    ∑ w : Fin n → β, ∑ b : β, splitLast law w b = 1 := by
  unfold splitLast
  rw [← sum_snoc]
  exact hsum

theorem fstMarginal_splitLast_nonneg {n : ℕ} {law : (Fin (n + 1) → β) → ℝ}
    (hnn : ∀ w, 0 ≤ law w) (w : Fin n → β) :
    0 ≤ fstMarginal (splitLast law) w :=
  Finset.sum_nonneg fun b _ => splitLast_nonneg hnn w b

theorem fstMarginal_splitLast_sum {n : ℕ} {law : (Fin (n + 1) → β) → ℝ}
    (hsum : ∑ w, law w = 1) :
    ∑ w : Fin n → β, fstMarginal (splitLast law) w = 1 :=
  splitLast_sum hsum

/-! ## The independence bound -/

/-- **Independence bound on entropy.**  A law on words of length `n` has
entropy at most the sum of the entropies of its coordinate marginals.
Equality would say the coordinates are independent; the inequality holds
always. -/
theorem entropy_le_sum_coordMarginal :
    ∀ (n : ℕ) (law : (Fin n → β) → ℝ), (∀ w, 0 ≤ law w) → (∑ w, law w = 1) →
      entropy law ≤ ∑ i : Fin n, entropy (coordMarginal law i) := by
  intro n
  induction n with
  | zero =>
    intro law _ hsum
    rw [Finset.univ_unique, Finset.sum_singleton] at hsum
    unfold entropy
    rw [Finset.univ_unique, Finset.sum_singleton, hsum, shannon_one]
    simp
  | succ n ih =>
    intro law hnn hsum
    have hjn : ∀ w b, 0 ≤ splitLast law w b := splitLast_nonneg hnn
    have hjs : ∑ w : Fin n → β, ∑ b : β, splitLast law w b = 1 :=
      splitLast_sum hsum
    -- The entropy of the word law is the joint entropy of the split.
    have hsplit : entropy law = jointEntropy (splitLast law) := by
      unfold entropy jointEntropy splitLast
      exact sum_snoc _
    -- Two-variable subadditivity at this level.
    have hsub := jointEntropy_le_add hjn hjs
    -- The inductive hypothesis, applied to the prefix law.
    have hih := ih (fstMarginal (splitLast law))
      (fstMarginal_splitLast_nonneg hnn) (fstMarginal_splitLast_sum hsum)
    rw [hsplit]
    have hlast : entropy (sndMarginal (splitLast law))
        = entropy (coordMarginal law (Fin.last n)) := by
      rw [sndMarginal_splitLast]
    have hrest : ∑ i : Fin n, entropy (coordMarginal (fstMarginal (splitLast law)) i)
        = ∑ i : Fin n, entropy (coordMarginal law i.castSucc) :=
      Finset.sum_congr rfl fun i _ => by
        rw [coordMarginal_fstMarginal_splitLast]
    rw [hrest] at hih
    rw [Fin.sum_univ_castSucc]
    linarith [hsub, hih, hlast.ge, hlast.le]

/-! ## Product laws on words: memorylessness

A family of per-coordinate laws induces a product law on words.  Its
normalization and its entropy both factor, the latter giving exactly the
additivity that makes a product channel memoryless. -/

/-- The product law on words induced by a family of per-coordinate laws. -/
def productLaw {n : ℕ} (rows : Fin n → β → ℝ) : (Fin n → β) → ℝ :=
  fun w => ∏ i, rows i (w i)

/-- Peeling the last coordinate off a product law leaves a product law. -/
theorem productLaw_snoc {n : ℕ} (rows : Fin (n + 1) → β → ℝ)
    (w : Fin n → β) (b : β) :
    productLaw rows (Fin.snoc w b)
      = productLaw (fun i => rows i.castSucc) w * rows (Fin.last n) b := by
  unfold productLaw
  rw [Fin.prod_univ_castSucc]
  simp

theorem productLaw_nonneg {n : ℕ} {rows : Fin n → β → ℝ}
    (hnn : ∀ i b, 0 ≤ rows i b) (w : Fin n → β) : 0 ≤ productLaw rows w :=
  Finset.prod_nonneg fun i _ => hnn i (w i)

/-- The mass of a product law factors as the product of the row masses. -/
theorem sum_productLaw :
    ∀ (n : ℕ) (rows : Fin n → β → ℝ),
      ∑ w : Fin n → β, productLaw rows w = ∏ i, ∑ b, rows i b := by
  intro n
  induction n with
  | zero =>
    intro rows
    rw [Finset.univ_unique, Finset.sum_singleton]
    simp [productLaw]
  | succ n ih =>
    intro rows
    rw [sum_snoc]
    have hrow : ∀ w ∈ (Finset.univ : Finset (Fin n → β)),
        ∑ b, productLaw rows (Fin.snoc w b)
          = productLaw (fun i => rows i.castSucc) w * ∑ b, rows (Fin.last n) b := by
      intro w _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => productLaw_snoc rows w b
    rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul, ih, Fin.prod_univ_castSucc]

/-- **Entropy is additive across coordinates of a product law.**  This is
memorylessness: independent uses contribute independently to uncertainty. -/
theorem entropy_productLaw :
    ∀ (n : ℕ) (rows : Fin n → β → ℝ), (∀ i b, 0 ≤ rows i b) →
      (∀ i, ∑ b, rows i b = 1) →
      entropy (productLaw rows) = ∑ i : Fin n, entropy (rows i) := by
  intro n
  induction n with
  | zero =>
    intro rows _ _
    unfold entropy
    rw [Finset.univ_unique, Finset.sum_singleton]
    simp [productLaw]
  | succ n ih =>
    intro rows hnn hsum
    have hrest : ∀ (i : Fin n) (b : β), 0 ≤ rows (Fin.castSucc i) b :=
      fun i b => hnn _ b
    have hrests : ∀ i : Fin n, ∑ b, rows (Fin.castSucc i) b = 1 := fun i => hsum _
    have hprefix : ∑ w : Fin n → β, productLaw (fun i => rows i.castSucc) w = 1 := by
      rw [sum_productLaw]
      simp [hrests]
    -- The split of a product law is the product of the prefix law and the last row.
    have hsplit : entropy (productLaw rows)
        = jointEntropy (fun (w : Fin n → β) (b : β) =>
            productLaw (fun i => rows i.castSucc) w * rows (Fin.last n) b) := by
      unfold entropy jointEntropy
      rw [sum_snoc]
      exact Finset.sum_congr rfl fun w _ =>
        Finset.sum_congr rfl fun b _ => by rw [productLaw_snoc]
    rw [hsplit, jointEntropy_product (productLaw_nonneg hrest)
      (fun b => hnn (Fin.last n) b) hprefix (hsum (Fin.last n)),
      ih (fun i => rows i.castSucc) hrest hrests, Fin.sum_univ_castSucc]

/-! ## The input/output joint law of a memoryless channel -/

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The word-level joint law of an input prior and a memoryless channel:
choose an input word from the prior, then pass it through the channel
coordinatewise and independently. -/
def channelJoint {n : ℕ} (prior : (Fin n → α) → ℝ) (K : α → β → ℝ) :
    (Fin n → α) → (Fin n → β) → ℝ :=
  fun x y => prior x * productLaw (fun i => K (x i)) y

/-- The input marginal of the channel joint is the prior it was built from. -/
theorem fstMarginal_channelJoint {n : ℕ} (prior : (Fin n → α) → ℝ)
    (K : α → β → ℝ) (hK : ∀ a, ∑ b, K a b = 1) :
    fstMarginal (channelJoint prior K) = prior := by
  funext x
  unfold fstMarginal channelJoint
  rw [← Finset.mul_sum, sum_productLaw]
  simp [hK]

/-- The cellwise form of the memoryless conditional entropy identity. -/
theorem condEntropy_cell_channel {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (if p * q = 0 then 0 else (p * q) * Real.log (p / (p * q)))
      = p * shannon q := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hq0 : q = 0
  · simp [hq0]
  · have hpq : p * q ≠ 0 := mul_ne_zero hp0 hq0
    simp only [hpq, if_false, shannon]
    rw [show p / (p * q) = q⁻¹ by field_simp]
    ring

/-- **Memoryless conditional entropy.**  Conditioned on the input word, the
remaining uncertainty in the output word is the prior-average of the summed
per-coordinate row entropies.  Nothing about the channel accumulates across
uses; this is exactly what memorylessness means. -/
theorem condEntropy_channelJoint {n : ℕ} (prior : (Fin n → α) → ℝ)
    (K : α → β → ℝ) (hpn : ∀ x, 0 ≤ prior x) (hKn : ∀ a b, 0 ≤ K a b)
    (hK : ∀ a, ∑ b, K a b = 1) :
    condEntropy (channelJoint prior K)
      = ∑ x : Fin n → α, prior x * ∑ i : Fin n, entropy (K (x i)) := by
  unfold condEntropy
  rw [fstMarginal_channelJoint prior K hK]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcell : ∀ y ∈ (Finset.univ : Finset (Fin n → β)),
      (if channelJoint prior K x y = 0 then 0
        else channelJoint prior K x y
          * Real.log (prior x / channelJoint prior K x y))
        = prior x * shannon (productLaw (fun i => K (x i)) y) :=
    fun y _ => condEntropy_cell_channel (hpn x)
      (productLaw_nonneg (fun i b => hKn _ b) y)
  rw [Finset.sum_congr rfl hcell, ← Finset.mul_sum]
  congr 1
  exact entropy_productLaw n (fun i => K (x i)) (fun i b => hKn _ b)
    (fun i => hK _)

/-! ## Reindexing: from a prior-average to per-coordinate conditional entropies -/

/-- Averaging a function of the `i`-th symbol against a law on words is the
same as averaging it against that law's `i`-th coordinate marginal. -/
theorem sum_apply_coord {n : ℕ} (prior : (Fin n → α) → ℝ) (i : Fin n)
    (f : α → ℝ) :
    ∑ x : Fin n → α, prior x * f (x i)
      = ∑ a : α, coordMarginal prior i a * f a := by
  unfold coordMarginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  symm
  rw [Finset.sum_eq_single (x i)]
  · simp
  · intro a _ hne
    simp [Ne.symm hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Memoryless conditional entropy, single-letterized.**  The conditional
entropy of the output word given the input word is the sum, over coordinates,
of the conditional entropy of that coordinate given its own input symbol. -/
theorem condEntropy_channelJoint_coord {n : ℕ} (prior : (Fin n → α) → ℝ)
    (K : α → β → ℝ) (hpn : ∀ x, 0 ≤ prior x) (hKn : ∀ a b, 0 ≤ K a b)
    (hK : ∀ a, ∑ b, K a b = 1) :
    condEntropy (channelJoint prior K)
      = ∑ i : Fin n, ∑ a : α, coordMarginal prior i a * entropy (K a) := by
  rw [condEntropy_channelJoint prior K hpn hKn hK]
  have hswap : ∑ x : Fin n → α, prior x * ∑ i : Fin n, entropy (K (x i))
      = ∑ i : Fin n, ∑ x : Fin n → α, prior x * entropy (K (x i)) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  exact Finset.sum_congr rfl fun i _ => sum_apply_coord prior i (fun a => entropy (K a))

/-! ## The `n`-use bound -/

theorem channelJoint_nonneg {n : ℕ} {prior : (Fin n → α) → ℝ} {K : α → β → ℝ}
    (hpn : ∀ x, 0 ≤ prior x) (hKn : ∀ a b, 0 ≤ K a b) (x : Fin n → α)
    (y : Fin n → β) : 0 ≤ channelJoint prior K x y :=
  mul_nonneg (hpn x) (productLaw_nonneg (fun i b => hKn _ b) y)

theorem sum_channelJoint {n : ℕ} {prior : (Fin n → α) → ℝ} {K : α → β → ℝ}
    (hps : ∑ x, prior x = 1) (hK : ∀ a, ∑ b, K a b = 1) :
    ∑ x : Fin n → α, ∑ y : Fin n → β, channelJoint prior K x y = 1 := by
  have h : ∀ x ∈ (Finset.univ : Finset (Fin n → α)),
      ∑ y : Fin n → β, channelJoint prior K x y = prior x := by
    intro x _
    have := congrFun (fstMarginal_channelJoint prior K hK) x
    exact this
  rw [Finset.sum_congr rfl h]
  exact hps

/-- **The `n`-use bound (single-letterization).**  For a memoryless channel and
any prior on input words, the information the output word carries about the
input word is at most the sum, over coordinates, of the information a single
use carries.  Bounding each bracket by the one-use capacity then gives the
familiar `I(Xⁿ;Yⁿ) ≤ n·C`. -/
theorem mutualInfo_channelJoint_le {n : ℕ} (prior : (Fin n → α) → ℝ)
    (K : α → β → ℝ) (hpn : ∀ x, 0 ≤ prior x) (hps : ∑ x, prior x = 1)
    (hKn : ∀ a b, 0 ≤ K a b) (hK : ∀ a, ∑ b, K a b = 1) :
    mutualInfo (channelJoint prior K)
      ≤ ∑ i : Fin n,
          (entropy (coordMarginal (sndMarginal (channelJoint prior K)) i)
            - ∑ a : α, coordMarginal prior i a * entropy (K a)) := by
  have hnn := channelJoint_nonneg (prior := prior) (K := K) hpn hKn
  have hsum := sum_channelJoint (prior := prior) (K := K) hps hK
  -- The output word law is a distribution, so the independence bound applies.
  have houtnn : ∀ y, 0 ≤ sndMarginal (channelJoint prior K) y :=
    fun y => Finset.sum_nonneg fun x _ => hnn x y
  have houts : ∑ y, sndMarginal (channelJoint prior K) y = 1 := by
    rw [sum_sndMarginal]; exact hsum
  have hind := entropy_le_sum_coordMarginal n
    (sndMarginal (channelJoint prior K)) houtnn houts
  rw [mutualInfo_eq_sub_condEntropy hnn,
    condEntropy_channelJoint_coord prior K hpn hKn hK,
    Finset.sum_sub_distrib]
  linarith

section Verification

#print axioms sum_apply_coord
#print axioms condEntropy_channelJoint_coord
#print axioms mutualInfo_channelJoint_le
#print axioms fstMarginal_channelJoint
#print axioms condEntropy_channelJoint
#print axioms sum_productLaw
#print axioms entropy_productLaw
#print axioms sum_snoc
#print axioms sndMarginal_splitLast
#print axioms coordMarginal_fstMarginal_splitLast
#print axioms entropy_le_sum_coordMarginal

end Verification

end

end TranscendenceTower.FiniteInformation
