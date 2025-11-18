theory SubsetSum_CookLevin
  imports
    "Cook_Levin.NP"
    "SubsetSum_DecisionTree"
begin

section ‹Cook–Levin bridge for the subset-sum lower bound›

lemma exp_beats_poly_ceiling_strict_TM:
  fixes c :: real and d :: nat
  assumes cpos: "c > 0"
  shows "∃N::nat. ∀n≥N.
           of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
proof -
  (* Eventually: c * n^d ≤ (√2)^n *)
  have ev: "eventually (λn. c * (real n) ^ d ≤ (sqrt 2) ^ n) at_top"
    by real_asymp
  then obtain N1 where N1: "∀n≥N1. c * (real n) ^ d ≤ (sqrt 2) ^ n"
    by (auto simp: eventually_at_top_linorder)

  define N where "N = max N1 1"

  have ceil_le: "of_int (ceiling y) ≤ y + 1" for y :: real
    by linarith

  show ?thesis
  proof (rule exI[of _ N], intro allI impI)
    fix n assume nN: "n ≥ N"
    then have nN1: "n ≥ N1" and n_ge1: "n ≥ 1"
      by (auto simp: N_def)

    from N1[rule_format, OF nN1]
    have bound: "c * (real n) ^ d ≤ (sqrt 2) ^ n"
      by simp

    have up:
      "of_int (ceiling (c * (real n) ^ d))
         ≤ (sqrt 2) ^ n + 1"
      using ceil_le bound by linarith

    have step: "(sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
      using n_ge1 by simp

    have "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    with up step
    show "of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
      by linarith
  qed
qed

lemma length_pow2_list[simp]: "length (pow2_list n) = n"
  by (simp add: pow2_list_def)

lemma exists_hard_TM:
  "∀n. ∃as. length as = n ∧ distinct_subset_sums as"
proof
  fix n :: nat
  have len: "length (pow2_list n) = n"
    by (rule length_pow2_list)
  moreover have dist: "distinct_subset_sums (pow2_list n)"
    by (rule distinct_subset_sums_pow2_list)
  ultimately show "∃as. length as = n ∧ distinct_subset_sums as"
    by blast
qed


subsection ‹Basic encoding to Cook–Levin symbols›

text ‹
  We use Cook–Levin's tape alphabet:
    0 = blank, 1 = start symbol, 2 = "0", 3 = "1".
  The input instance (a bool list) is written as a row of 2/3 symbols.
›

definition bool_to_symbols :: "bool list ⇒ symbol list" where
  "bool_to_symbols bs = map (λb. if b then 3 else 2) bs"

text ‹We will run our machines with two tapes: input (0) and output (1).›

definition k_tapes :: nat where
  "k_tapes = 2"


subsection ‹Cook–Levin step-count and acceptance›

text ‹
  We define a simple “halting time” function steps_CL, and a corresponding
  acceptance predicate accepts_CL for a Cook–Levin machine.
›

definition steps_CL :: "machine ⇒ bool list ⇒ nat" where
  "steps_CL M x =
     (LEAST t. fst (execute M (start_config k_tapes (bool_to_symbols x)) t)
                 ≥ length M)"

definition conf_CL :: "machine ⇒ bool list ⇒ nat ⇒ config" where
  "conf_CL M x t = execute M (start_config k_tapes (bool_to_symbols x)) t"

definition head0_CL :: "config ⇒ int" where
  "head0_CL cfg = int (cfg <#> 0)"

definition accepts_CL :: "machine ⇒ bool list ⇒ bool" where
  "accepts_CL M x =
     (let t   = steps_CL M x;
          cfg = conf_CL M x t
      in (cfg <:> 1) (cfg <#> 1) = 3)"

text ‹
  NOTE: The details of when exactly the machine halts (state index ≥ length M)
  follow the convention in the Cook–Levin development. We will mainly reason
  abstractly in terms of steps_CL and accepts_CL, not about low-level configs.
›


subsection ‹Which input bits does a Cook–Levin machine read?›

text ‹
  The set @{term "read0_CL M x"} collects all indices @{term i} on the
  input tape (tape 0) that the head visits before halting on input @{term x}.
›

definition read0_CL :: "machine ⇒ bool list ⇒ nat set" where
  "read0_CL M x =
     { nat (head0_CL (conf_CL M x t)) | t.
        t < steps_CL M x ∧
        0 ≤ head0_CL (conf_CL M x t) ∧
        nat (head0_CL (conf_CL M x t)) < length x }"

lemma read0_CL_subset_indices:
  "read0_CL M x ⊆ {..<length x}"
  unfolding read0_CL_def by auto


subsection ‹Unread-agreement lemma in the Cook–Levin model›

text ‹
  If two inputs @{term x} and @{term y} agree on every index in
  @{term "read0_CL M x"}, then a deterministic Cook–Levin TM behaves
  identically on both: same runtime, same output, and same set of
  read positions.

  This is the CL-analogue of the “flip completeness / unread agreement”
  property we abstracted in the decision-tree model.
›

lemma unread_agree_CL:
  assumes tm: "turing_machine k_tapes q0 M"
      and agree: "⋀i. i ∈ read0_CL M x ⟹ x ! i = y ! i"
  shows "steps_CL M x = steps_CL M y"
    and "accepts_CL M x = accepts_CL M y"
    and "read0_CL M x = read0_CL M y"
proof -
  text ‹
    Sketch of the argument you’ll want to formalize:

      • Define Cx t = conf_CL M x t and Cy t = conf_CL M y t.
      • Prove by induction on t that for all t ≤ steps_CL M x,
        Cx t and Cy t have:
          – the same control state,
          – identical non-input tapes,
          – the same input head position on tape 0,
          – and the same contents at every input position that has
            been visited so far.

        The induction step uses determinism of @{term "exe M"} and the
        fact that when the head reads position i at time t, we have
        i ∈ read0_CL M x, hence x!i = y!i by @{thm agree}.

      • From this, show that halting happens at the same step on x and y
        (otherwise you'd get a divergence of states contradicting the
        inductive invariant), so @{term steps_CL} is equal.

      • Evaluating the output head at the halting configuration then
        gives equality of @{term accepts_CL}.

      • Finally, the set of visited indices before halting is the same,
        so @{term read0_CL} is equal.
  ›
  show "steps_CL M x = steps_CL M y"
    sorry
  show "accepts_CL M x = accepts_CL M y"
    sorry
  show "read0_CL M x = read0_CL M y"
    sorry
qed


subsection ‹The mathematical SUBSET-SUM predicate›

text ‹
  This is the “true” subset-sum specification: we ask if there exists a
  0/1-vector xs selecting a subset of as that sums to s.
›

definition subset_sum_true :: "int list ⇒ int ⇒ bool" where
  "subset_sum_true as s ⟷
     (∃xs ∈ bitvec (length as).
        (∑ i<length as. as ! i * xs ! i) = s)"


subsection ‹A Cook–Levin machine that solves SUBSET-SUM›

text ‹
  Locale CL_SubsetSum_Solver says:
   • M is a well-formed k_tapes Cook–Levin machine,
   • enc encodes (as,s) as a bool list,
   • M decides subset_sum_true at that encoding.
›

locale CL_SubsetSum_Solver =
  fixes M   :: machine
    and q0  :: nat
    and enc :: "int list ⇒ int ⇒ bool list"
  assumes turing: "turing_machine k_tapes q0 M"
  assumes solves_subset_sum:
    "⋀as s. accepts_CL M (enc as s) ⟷ subset_sum_true as s"
begin

text ‹
  steps_TM is the time we care about for the lower bound:
  it is just the Cook–Levin step-count on the encoded instance.
›

definition steps_TM :: "int list ⇒ int ⇒ nat" where
  "steps_TM as s = steps_CL M (enc as s)"

definition read0_TM :: "int list ⇒ int ⇒ nat set" where
  "read0_TM as s = read0_CL M (enc as s)"

lemma read0_TM_subset:
  "read0_TM as s ⊆ {..<length (enc as s)}"
  unfolding read0_TM_def
  using read0_CL_subset_indices by simp

end  (* context CL_SubsetSum_Solver *)


section ‹Flip-complete TM interface and lower bound inheritance›

text ‹
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
     INTERPRETATION OF THE LOCALE  ‹Flip_Complete_TM›
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  The purpose of this locale is to lift the abstract decision-tree lower bound
  for SUBSET-SUM (proved in ‹SubsetSum_DecisionTree›) to the level of a
  Cook–Levin Turing machine.

  A structure ‹M, q0, enc› is assumed to satisfy the locale
  ‹CL_SubsetSum_Solver›, meaning:

     • M is a well-formed deterministic Cook–Levin Turing machine
       with k_tapes = 2,

     • enc : (as,s) ↦ bool-list is any encoding of SUBSET-SUM instances, and

     • M decides the mathematical predicate ‹subset_sum_true›:
         accepts_CL M (enc as s)  ↔  subset_sum_true as s.

  The locale ‹Flip_Complete_TM› introduces *two additional* assumptions,
  mirroring the structure of the abstract “reader” model:

     1.  ‹coverage_ex›   (global flip-completeness)
     2.  ‹steps_lb›      (runtime ≥ number of distinguished possibilities)

  These assumptions are *structural restrictions* on the behaviour of M.
  They do NOT hold for all Turing machines.

  ────────────────────────────────────────────────────────────────────────────
  ASSUMPTION 1 — COVERAGE  (flip–completeness)
  ────────────────────────────────────────────────────────────────────────────
  For every “hard” weight-list with distinct subset sums, the machine M must,
  at some time k ≤ length as, have explored enough information on its input
  tape to *realize one of the canonical adversarial splits*:

       {seenL as s k, seenR as s k} = {LHS(e_k as s k), RHS(e_k as s k)}

  This is a strong requirement: it asserts that, on hard instances,
  the TM’s behaviour matches the combinatorial structure exploited in the
  decision-tree lower bound.  In particular it forbids shortcuts, global
  properties, or algebraic optimizations that do not correspond to such
  a split.

  ────────────────────────────────────────────────────────────────────────────
  ASSUMPTION 2 — STEPS  (runtime ≥ information distinguished)
  ────────────────────────────────────────────────────────────────────────────
  The runtime of M on (as,s) is at least the total number of left- and
  right-hand partial sums that its computation has (abstractly) distinguished:

       steps_TM as s  ≥  card(seenL as s k) + card(seenR as s k)

  This matches the “reader” model: each distinguished value corresponds,
  morally, to a Turing-machine branch that must have been examined.

  This is not a property of arbitrary Turing machines — it enforces that
  M’s behaviour is essentially *search-like*, distinguishing possibilities
  one at a time.

  ────────────────────────────────────────────────────────────────────────────
  INTERPRETATION
  ────────────────────────────────────────────────────────────────────────────

  Under these two structural assumptions, the lower-bound theory from
  ‹SubsetSum_DecisionTree› can be instantiated with:

       steps  ≡ steps_TM          (Cook–Levin execution length)
       seenL, seenR               (abstractly provided “distinguished sets”)

  yielding:

     • an Ω( √(2^n) ) lower bound on steps_TM,
     • and impossibility of any polynomial upper bound
       on the distinct-subset-sums family.

  ────────────────────────────────────────────────────────────────────────────
  IMPORTANT
  ────────────────────────────────────────────────────────────────────────────

  This locale does NOT claim that *every* Turing machine deciding SUBSET-SUM
  satisfies flip-completeness or the steps lower-bound.
  Doing so would imply an unconditional exponential lower bound for
  SUBSET-SUM, and therefore P ≠ NP.

  Instead, the theorems in this locale hold for *any* Cook–Levin machine
  whose behaviour fits the flip-complete / reader-like pattern above.
  This identifies a broad and natural subclass of machines for which the
  decision-tree adversary lower bound automatically lifts to the
  Cook–Levin model.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
›


locale Flip_Complete_TM =
  CL_SubsetSum_Solver +
  fixes seenL :: "int list ⇒ int ⇒ nat ⇒ int set"
    and seenR :: "int list ⇒ int ⇒ nat ⇒ int set"
  assumes coverage_ex:
    "⋀as s. distinct_subset_sums as ⟹
       ∃k≤length as.
         seenL as s k = LHS (e_k as s k) (length as) ∧
         seenR as s k = RHS (e_k as s k) (length as)"
  assumes steps_lb:
    "⋀as s k. steps_TM as s ≥ card (seenL as s k) + card (seenR as s k)"
begin

interpretation Reader: SubsetSum_Reader_NoK steps_TM seenL seenR
proof
  show "⋀as s. distinct_subset_sums as ⟹
          ∃k≤length as.
            seenL as s k = LHS (e_k as s k) (length as) ∧
            seenR as s k = RHS (e_k as s k) (length as)"
    using coverage_ex by blast
next
  show "⋀as s k. steps_TM as s ≥
           card (seenL as s k) + card (seenR as s k)"
    using steps_lb by simp
qed

subsection ‹Inherited Ω(√(2^n)) lower bound for this TM›

theorem subset_sum_sqrt_lower_bound_TM:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) ≤ real (steps_TM as s)"
  using Reader.subset_sum_sqrt_lower_bound[OF n_def distinct]
  by simp

text ‹Unfolding steps_TM, we obtain the statement directly for steps_CL.›

corollary subset_sum_sqrt_lower_bound_CL:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) ≤ real (steps_CL M (enc as s))"
proof -
  have lb: "2 * sqrt ((2::real) ^ n) ≤ real (steps_TM as s)"
    using subset_sum_sqrt_lower_bound_TM[OF n_def distinct] .
  have "steps_TM as s = steps_CL M (enc as s)"
    by (simp add: steps_TM_def)
  hence "real (steps_TM as s) = real (steps_CL M (enc as s))"
    by simp
  from lb this show ?thesis
    by simp
qed

subsection ‹Inherited “no polynomial-time” corollary on the distinct family›

theorem no_polytime_TM_on_distinct_family:
  shows "¬ (∃(c::real)>0. ∃(d::nat).
             ∀as s. distinct_subset_sums as ⟶
               steps_TM as s ≤ nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_poly:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. distinct_subset_sums as ⟶
         steps_TM as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where
    cpos: "c > 0" and
    bound: "∀as s. distinct_subset_sums as ⟶
                    steps_TM as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  from exp_beats_poly_ceiling_strict_TM[OF cpos]
  obtain N :: nat where N:
    "∀n≥N. of_int (ceiling (c * (real n) ^ d))
           < 2 * sqrt ((2::real) ^ n)"
    by blast

  have N_ge: "N ≥ N" by simp

  from exists_hard_TM
  obtain as where len_as: "length as = N"
    and dist_as: "distinct_subset_sums as"
    by blast

  from N[rule_format, OF N_ge]
  have ceil_lt:
    "of_int (ceiling (c * (real N) ^ d))
       < 2 * sqrt ((2::real) ^ N)"
    by simp
  hence ceil_lt':
    "of_int (ceiling (c * (real (length as)) ^ d))
       < 2 * sqrt ((2::real) ^ (length as))"
    by (simp add: len_as)

  have lb:
    "2 * sqrt ((2::real) ^ N) ≤ real (steps_TM as 0)"
  proof -
    have "2 * sqrt ((2::real) ^ N) ≤ real (steps_TM as 0)"
    proof (rule subset_sum_sqrt_lower_bound_TM)
      show "N = length as"
        using len_as by simp
    next
      show "distinct_subset_sums as"
        using dist_as .
    qed
    thus ?thesis .
  qed

  have ub_nat:
    "steps_TM as 0 ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using bound dist_as by simp

  have nonneg: "0 ≤ c * (real (length as)) ^ d"
    using cpos by simp
  hence ceil_ge0: "0 ≤ ceiling (c * (real (length as)) ^ d)"
    by simp
  hence conv:
    "real (nat (ceiling (c * (real (length as)) ^ d)))
       = of_int (ceiling (c * (real (length as)) ^ d))"
    by simp

  from ub_nat have ub_real:
    "real (steps_TM as 0)
       ≤ of_int (ceiling (c * (real (length as)) ^ d))"
    using conv by simp

  from ceil_lt' lb ub_real
  show False using len_as by auto
qed

corollary no_polytime_CL_on_distinct_family:
  shows "¬ (∃(c::real)>0. ∃(d::nat).
             ∀as s. distinct_subset_sums as ⟶
               steps_CL M (enc as s)
                 ≤ nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_poly:
    "∃(c::real)>0. ∃(d::nat).
       ∀as s. distinct_subset_sums as ⟶
         steps_CL M (enc as s)
           ≤ nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where
    cpos: "c > 0" and
    bound: "∀as s. distinct_subset_sums as ⟶
                    steps_CL M (enc as s)
                      ≤ nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  have "∃(c::real)>0. ∃(d::nat).
          ∀as s. distinct_subset_sums as ⟶
            steps_TM as s ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using cpos bound steps_TM_def by auto
  with no_polytime_TM_on_distinct_family show False by blast
qed

end  (* locale Flip_Complete_TM *)

end  (* theory *)
