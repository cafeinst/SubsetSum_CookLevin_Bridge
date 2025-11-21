theory SubsetSum_CookLevin
  imports
    "Cook_Levin.NP"
    "SubsetSum_DecisionTree"
begin

section ‹Cook–Levin bridge for the subset-sum lower bound›

text ‹
  STRUCTURE OF THIS THEORY

  • On the decision-tree side, the theory ‹SubsetSum_DecisionTree› proves
    a lower bound of Ω(√(2^n)) for any “flip-complete reader” model of
    SUBSET-SUM.  This is phrased abstractly in terms of a step function
    ‹steps› and canonical LHS/RHS partial-sum sets ‹LHS› and ‹RHS›.

  • In this file, we connect that abstract model to the concrete
    Cook–Levin Turing-machine model (‹Cook_Levin.NP›) in several layers:

      – ‹CL_SubsetSum_Solver›:
          A machine ‹M› with encoding ‹enc› that *correctly decides* the
          mathematical predicate ‹subset_sum_true›.

      – ‹Eq_ReadLR_SubsetSum_Solver›:
          Strengthens ‹CL_SubsetSum_Solver› by saying that ‹M› decides
          SUBSET-SUM via an equality of two “sides” (‹lhs›, ‹rhs›), and
          that, on distinct-subset-sums instances, it must read at least
          one bit from the part of the input encoding the left side and
          at least one bit from the part encoding the right side.  This
          captures the informal “must look at L and R” requirement.

      – ‹LR_Read_TM›:
          A more structural assumption on ‹M›, still over the concrete
          Cook–Levin model, which directly instantiates the abstract
          decision-tree axiom ‹SubsetSum_Lemma1›.  Concretely, it assumes
          that on any hard instance of length ‹n›, the runtime
          ‹steps_TM as s› is at least

              card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)

          for some canonical split index ‹k ≤ n›.  Inside this locale we
          inherit the Ω(√(2^n)) lower bound and the “no polynomial-time”
          corollaries.

      – ‹All_SubsetSum_Polytime_LR_Read›:
          A meta-assumption saying that *every* polynomial-time CL solver
          for SUBSET-SUM satisfies the ‹LR_Read_TM› axiom.  Under this
          single assumption, we conclude that there is no polynomial-time
          Cook–Levin machine deciding SUBSET-SUM.

  The main point is that all nontrivial lower-bound reasoning is carried
  out *inside* the reader-style locales (‹SubsetSum_Lemma1› on the
  abstract side, and ‹LR_Read_TM› on the Cook–Levin side).  The gap to a
  full P ≠ NP statement is precisely the meta-assumption that every
  polynomial-time solver satisfies the LR-read lower-bound axiom.
›

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

subsection ‹Configuration agreement and unread positions›

text ‹
  Two configurations agree except possibly at position i on tape 0.
  This is a convenient concept if one wants to reason about how a single
  unread bit on the input tape can be flipped without affecting the
  rest of the machine's behaviour.  In this theory we will *not* prove
  a general unread-flip lemma for all Cook–Levin machines; instead,
  we package the desired unread-agreement property as a locale axioms
  for the particular machines we care about (see below).
›

definition configs_agree_except_at :: "nat ⇒ config ⇒ config ⇒ bool" where
  "configs_agree_except_at i c1 c2 ⟷
     fst c1 = fst c2 ∧
     ||c1|| = ||c2|| ∧
     (∀t. 0 < t ⟶ t < ||c1|| ⟶
         c1 <:> t = c2 <:> t ∧
         c1 <#> t = c2 <#> t) ∧
     c1 <#> 0 = c2 <#> 0 ∧
     (∀pos. pos ≠ i ⟶ (c1 <:> 0) pos = (c2 <:> 0) pos)"

text ‹Flipping a bit in a bool list›

definition flip_bool_list :: "bool list ⇒ nat ⇒ bool list" where
  "flip_bool_list xs i =
     (if i < length xs then xs[i := (¬ xs!i)] else xs)"

lemma bool_to_symbols_flip_outside:
  assumes "j < length x" "j ≠ i"
  shows "bool_to_symbols (flip_bool_list x i) ! j
       = bool_to_symbols x ! j"
  using assms
  unfolding bool_to_symbols_def flip_bool_list_def
  by (auto simp: nth_list_update)

lemma flip_bool_list_length[simp]:
  "length (flip_bool_list xs i) = length xs"
  by (simp add: flip_bool_list_def)

lemma flip_bool_list_eq_outside:
  assumes "j < length xs" "j ≠ i"
  shows "flip_bool_list xs i ! j = xs ! j"
  using assms
  by (simp add: flip_bool_list_def)

lemma head0_bounded:
  assumes "turing_machine k_tapes q0 M"
  assumes "t < steps_CL M x"
  shows   "head0_CL (conf_CL M x t) ≥ 0"
  unfolding head0_CL_def conf_CL_def
  by simp

subsection ‹Unread-agreement property as a locale axiom›

text ‹
  We now *axiomatize* the unread-flip agreement property for a given
  Cook–Levin machine.  Intuitively, this says:

    • if bit i of x is never read on tape 0 in the run of M on input x,
      then flipping that bit does not change whether M accepts.

  This is the Cook–Levin analogue of the “unread bits do not matter”
  property used on the decision-tree side.  It is *not* derivable for
  arbitrary machines from the raw Cook–Levin semantics, so we expose it
  as a separate locale that can be assumed for the particular solvers
  we care about.
›

locale Flip_Agreement_CL =
  fixes M :: machine and q0 :: nat
  assumes TM: "turing_machine k_tapes q0 M"
  assumes unread_agreement:
    "⋀x i. i < length x ⟹ i ∉ read0_CL M x
          ⟹ accepts_CL M x = accepts_CL M (flip_bool_list x i)"

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

subsection ‹Equation-based read requirement›

text ‹
  This locale expresses the idea that the machine decides SUBSET-SUM
  by checking equality of two “sides” of an equation.  Conceptually,
  there is some base equation

      l(as, s) = r(as, s)

  such that (as,s) is in the language iff this equation holds.  We allow
  the machine to work with any *equivalent* equation, e.g. of the form

      f(l(as,s)) = f(r(as,s))

  for some injective function f; all of this is abstracted into the
  two functions ‹lhs› and ‹rhs›, and the correctness assumption

      subset_sum_true as s ⟷ lhs as s = rhs as s.

  The sets ‹L_zone as s› and ‹R_zone as s› describe the input positions
  (in ‹enc as s›) that encode the left- and right-hand sides of this
  deciding equation.  The assumption ‹must_read_LR› then says:

      – on every distinct-subset-sums instance (as,s),
        the machine’s read set ‹read0_TM as s› intersects L_zone as s, and
      – it also intersects R_zone as s.

  In other words: on “hard” instances, the machine must read at least one
  bit from the part of the input encoding the left side and at least one
  bit from the part encoding the right side of some deciding equation
  equivalent to l = r.
›

locale Eq_ReadLR_SubsetSum_Solver =
  CL_SubsetSum_Solver M q0 enc
  for M :: machine and q0 :: nat
      and enc :: "int list ⇒ int ⇒ bool list" +
  fixes lhs rhs :: "int list ⇒ int ⇒ int"
    and L_zone R_zone :: "int list ⇒ int ⇒ nat set"
  assumes equation_correct:
    "⋀as s. subset_sum_true as s ⟷ (lhs as s = rhs as s)"
  assumes zones_wf:
    "⋀as s. L_zone as s ⊆ {..< length (enc as s)}"
    "⋀as s. R_zone as s ⊆ {..< length (enc as s)}"
    "⋀as s. L_zone as s ∩ R_zone as s = {}"
  assumes must_read_LR:
    "⋀as s. distinct_subset_sums as ⟹
        read0_TM as s ∩ L_zone as s ≠ {} ∧
        read0_TM as s ∩ R_zone as s ≠ {}"

text ‹
  RELATION TO THE ABSTRACT LOWER-BOUND AXIOM ‹LR_Read_TM›

  The locale ‹Eq_ReadLR_SubsetSum_Solver› isolates a concrete,
  adversary-style requirement:

    • SUBSET-SUM is decided via some equation
        lhs as s = rhs as s
      (up to injective re-encoding, e.g. ‹f (lhs as s) = f (rhs as s)›),

    • and on distinct-subset-sums instances the machine must read at
      least one bit from the part of the input encoding the “left side”
      and at least one bit from the part encoding the “right side”
      (‹L_zone as s› and ‹R_zone as s›).

  The locale ‹LR_Read_TM› below is a more structured, but still abstract,
  interface to the decision-tree lower bound.  Instead of talking about
  particular input zones, it assumes directly that for some canonical
  split index ‹k›, the runtime is at least

      card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)

  on any distinct-subset-sums instance of length ‹n›.  This matches the
  combinatorial structure exploited in ‹SubsetSum_DecisionTree› and is
  exactly what is needed to instantiate the abstract reader model.

  Intuitively, any machine satisfying the concrete “must read from L and
  R” condition of ‹Eq_ReadLR_SubsetSum_Solver› *and* aligning with the
  canonical LHS/RHS partial-sum splits should give rise to an instance of
  ‹LR_Read_TM›.  In this theory we keep that connection as a meta-level
  assumption (see the locales ‹All_SubsetSum_Polytime_LR_Read› and
  ‹All_SubsetSum_Polytime_Eq_ReadLR› below).  All formal lower-bound
  proofs are phrased inside ‹LR_Read_TM›, which is the Cook–Levin side
  of the flip-complete/reader-style model.
›


section ‹LR-read TM interface and lower bound inheritance›

text ‹
  A Cook–Levin machine is polynomial-time on SUBSET-SUM if its
  running time on the encoding of (as,s) is bounded by some polynomial
  in the length of the weight list as (≃ input size).  We take this
  as the basic complexity measure; the bit-length of the encoding
  ‹enc as s› is allowed to be some fixed polynomial in ‹length as›.
›

definition polytime_CL_machine
  :: "machine ⇒ (int list ⇒ int ⇒ bool list) ⇒ bool"
where
  "polytime_CL_machine M enc ⟷
     (∃(c::real)>0. ∃(d::nat).
        ∀as s. steps_CL M (enc as s)
               ≤ nat (ceiling (c * (real (length as)) ^ d)))"

locale LR_Read_TM =
  CL_SubsetSum_Solver M q0 enc
  for M :: machine and q0 :: nat
      and enc :: "int list ⇒ int ⇒ bool list" +
  assumes lemma1_ex_TM:
    "⋀as s n. n = length as ⟹ distinct_subset_sums as ⟹
       ∃k≤n.
         card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)
         ≤ steps_TM as s"
begin

text ‹
  The assumption ‹lemma1_ex_TM› is the formal version of:

    “On any hard (distinct-subset-sums) instance of length n,
     the way we canonically express the instance as an equality
     l = r using the splits e_k (or an injectively equivalent
     equation f(l) = f(r)) forces the machine to effectively
     distinguish all values on the left and right.”

  This corresponds to the informal requirement that the TM must
  “examine” at least one bit from the left-hand value and one
  bit from the right-hand value for each candidate equality.
›

interpretation Reader: SubsetSum_Lemma1 steps_TM
proof
  show "⋀as s n. n = length as ⟹ distinct_subset_sums as ⟹
           ∃k≤n.
             card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)
             ≤ steps_TM as s"
    by (rule lemma1_ex_TM)
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

end  (* locale LR_Read_TM *)


text ‹
  This locale captures a **meta-assumption**: whenever a Cook–Levin
  machine correctly decides SUBSET-SUM via an equation satisfying
  the “read one bit of L and one bit of R” requirement, *and* runs
  in polynomial time, then it also satisfies the more structured
  LR-read axiom of ‹LR_Read_TM›.

  Under this meta-assumption we can state the final lower bound using
  only the concrete Eq_ReadLR_SubsetSum_Solver hypothesis.
›

locale All_SubsetSum_Polytime_Eq_ReadLR =
  fixes M :: machine
    and q0 :: nat
    and enc :: "int list ⇒ int ⇒ bool list"
    and lhs rhs :: "int list ⇒ int ⇒ int"
    and L_zone R_zone :: "int list ⇒ int ⇒ nat set"
  assumes all_polytime_ReadLR_LR:
    "Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone ⟹
     polytime_CL_machine M enc ⟹
     LR_Read_TM M q0 enc"

context All_SubsetSum_Polytime_Eq_ReadLR
begin

theorem no_polytime_CL_subset_sum_ReadLR:
  assumes solver: "Eq_ReadLR_SubsetSum_Solver M q0 enc lhs rhs L_zone R_zone"
      and poly:   "polytime_CL_machine M enc"
  shows False
proof -
  from all_polytime_ReadLR_LR[OF solver poly]
  have lr: "LR_Read_TM M q0 enc" .

  interpret LR: LR_Read_TM M q0 enc
    by (rule lr)

  from poly obtain c d where
    cpos: "c > 0" and
    bound_all: "∀as s. steps_CL M (enc as s)
                      ≤ nat (ceiling (c * (real (length as)) ^ d))"
    unfolding polytime_CL_machine_def by blast

  have family_bound:
    "∃(c::real)>0. ∃(d::nat).
     ∀as s. distinct_subset_sums as ⟶
       steps_CL M (enc as s)
         ≤ nat (ceiling (c * (real (length as)) ^ d))"
    using cpos bound_all by blast

  from LR.no_polytime_CL_on_distinct_family
  have contradiction:
    "¬ (∃(c::real)>0. ∃(d::nat).
        ∀as s. distinct_subset_sums as ⟶
          steps_CL M (enc as s)
            ≤ nat (ceiling (c * (real (length as)) ^ d)))" .

  from contradiction family_bound show False
    by blast
qed

end
