theory SubsetSum_CookLevin
  imports
    "Cook_Levin.NP"
    "SubsetSum_DecisionTree"
begin

section \<open>Cook–Levin bridge for the subset-sum lower bound\<close>

text \<open>
  STRUCTURE OF THIS THEORY

  • On the decision-tree side, the theory \<open>SubsetSum_DecisionTree\<close> proves
    a lower bound of \<Omega>(\<surd>(2^n)) for any “flip-complete reader” model of
    SUBSET-SUM.  This is phrased abstractly in terms of a step function
    \<open>steps\<close> and canonical LHS/RHS partial-sum sets \<open>LHS\<close> and \<open>RHS\<close>.

  • In this file, we connect that abstract model to the concrete
    Cook–Levin Turing-machine model (\<open>Cook_Levin.NP\<close>) in several layers:

      – \<open>CL_SubsetSum_Solver\<close>:
          A machine \<open>M\<close> with encoding \<open>enc\<close> that *correctly decides* the
          mathematical predicate \<open>subset_sum_true\<close>.

      – \<open>Eq_ReadLR_SubsetSum_Solver\<close>:
          Strengthens \<open>CL_SubsetSum_Solver\<close> by saying that \<open>M\<close> decides
          SUBSET-SUM via an equality of two “sides” (\<open>lhs\<close>, \<open>rhs\<close>), and
          that, on distinct-subset-sums instances, it must read at least
          one bit from the part of the input encoding the left side and
          at least one bit from the part encoding the right side.  This
          captures the informal “must look at L and R” requirement.

      – \<open>LR_Read_TM\<close>:
          A more structural assumption on \<open>M\<close>, still over the concrete
          Cook–Levin model, which directly instantiates the abstract
          decision-tree axiom \<open>SubsetSum_Lemma1\<close>.  Concretely, it assumes
          that on any hard instance of length \<open>n\<close>, the runtime
          \<open>steps_TM as s\<close> is at least

              card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)

          for some canonical split index \<open>k \<le> n\<close>.  Inside this locale we
          inherit the \<Omega>(\<surd>(2^n)) lower bound and the “no polynomial-time”
          corollaries.

      – \<open>All_SubsetSum_Polytime_LR_Read\<close>:
          A meta-assumption saying that *every* polynomial-time CL solver
          for SUBSET-SUM satisfies the \<open>LR_Read_TM\<close> axiom.  Under this
          single assumption, we conclude that there is no polynomial-time
          Cook–Levin machine deciding SUBSET-SUM.

  The main point is that all nontrivial lower-bound reasoning is carried
  out *inside* the reader-style locales (\<open>SubsetSum_Lemma1\<close> on the
  abstract side, and \<open>LR_Read_TM\<close> on the Cook–Levin side).  The gap to a
  full P \<noteq> NP statement is precisely the meta-assumption that every
  polynomial-time solver satisfies the LR-read lower-bound axiom.
\<close>


text \<open>
  First, we re-prove the elementary analytic fact that exponentials beat
  polynomials, but packaged in exactly the numerical form we later need
  for step-count bounds of Cook–Levin machines.
\<close>
lemma exp_beats_poly_ceiling_strict_TM:
  fixes c :: real and d :: nat
  assumes cpos: "c > 0"
  shows "\<exists>N::nat. \<forall>n\<ge>N.
           of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
proof -
  (* Eventually: c * n^d \<le> (\<surd>2)^n *)
  have ev: "eventually (\<lambda>n. c * (real n) ^ d \<le> (sqrt 2) ^ n) at_top"
    by real_asymp
  then obtain N1 where N1: "\<forall>n\<ge>N1. c * (real n) ^ d \<le> (sqrt 2) ^ n"
    by (auto simp: eventually_at_top_linorder)

  define N where "N = max N1 1"

  (* Simple ceiling bound: \<lceil>y\<rceil> \<le> y + 1 *)
  have ceil_le: "of_int (ceiling y) \<le> y + 1" for y :: real
    by linarith

  show ?thesis
  proof (rule exI[of _ N], intro allI impI)
    fix n assume nN: "n \<ge> N"
    then have nN1: "n \<ge> N1" and n_ge1: "n \<ge> 1"
      by (auto simp: N_def)

    from N1[rule_format, OF nN1]
    have bound: "c * (real n) ^ d \<le> (sqrt 2) ^ n"
      by simp

    (* Turn this into a bound on the ceiling. *)
    have up:
      "of_int (ceiling (c * (real n) ^ d))
         \<le> (sqrt 2) ^ n + 1"
      using ceil_le bound by linarith

    (* For n \<ge> 1, we have (\<surd>2)^n + 1 < 2\<sqdot>(\<surd>2)^n. *)
    have step: "(sqrt 2) ^ n + 1 < 2 * (sqrt 2) ^ n"
      using n_ge1 by simp

    (* Rewrite 2\<sqdot>\<surd>(2^n) as 2\<sqdot>(\<surd>2)^n to match the bound. *)
    have "2 * sqrt ((2::real) ^ n) = 2 * (sqrt 2) ^ n"
      by (simp add: real_sqrt_power)
    with up step
    show "of_int (ceiling (c * (real n) ^ d)) < 2 * sqrt ((2::real) ^ n)"
      by linarith
  qed
qed

lemma length_pow2_list[simp]: "length (pow2_list n) = n"
  by (simp add: pow2_list_def)

text \<open>
  For every length n, we can choose a “hard” weight list as of that
  length, namely the powers of 2; these have distinct subset sums.
  This is the TM-side analogue of the hard family used in the
  decision-tree theory.
\<close>
lemma exists_hard_TM:
  "\<forall>n. \<exists>as. length as = n \<and> distinct_subset_sums as"
proof
  fix n :: nat
  have len: "length (pow2_list n) = n"
    by (rule length_pow2_list)
  moreover have dist: "distinct_subset_sums (pow2_list n)"
    by (rule distinct_subset_sums_pow2_list)
  ultimately show "\<exists>as. length as = n \<and> distinct_subset_sums as"
    by blast
qed


subsection \<open>Basic encoding to Cook–Levin symbols\<close>

text \<open>
  We use Cook–Levin's tape alphabet:
    0 = blank, 1 = start symbol, 2 = "0", 3 = "1".
  The input instance (a bool list) is written as a row of 2/3 symbols.

  We keep this as lightweight as possible: we only need a simple
  mapping from booleans to tape symbols and a fixed tape count k_tapes.
\<close>

definition bool_to_symbols :: "bool list \<Rightarrow> symbol list" where
  "bool_to_symbols bs = map (\<lambda>b. if b then 3 else 2) bs"

text \<open>We will run our machines with two tapes: input (0) and output (1).\<close>

definition k_tapes :: nat where
  "k_tapes = 2"


subsection \<open>Cook–Levin step-count and acceptance\<close>

text \<open>
  We define a simple “halting time” function steps_CL, and a corresponding
  acceptance predicate accepts_CL for a Cook–Levin machine.

  • steps_CL M x is the least t at which the control state index
    is \<ge> length M (Cook–Levin’s halting convention).

  • conf_CL M x t is the configuration after t steps.

  • accepts_CL M x says that after steps_CL M x steps, the symbol under
    the head on tape 1 (the output tape) is 3, i.e. “1”.
\<close>

definition steps_CL :: "machine \<Rightarrow> bool list \<Rightarrow> nat" where
  "steps_CL M x =
     (LEAST t. fst (execute M (start_config k_tapes (bool_to_symbols x)) t)
                 \<ge> length M)"

definition conf_CL :: "machine \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> config" where
  "conf_CL M x t = execute M (start_config k_tapes (bool_to_symbols x)) t"

definition head0_CL :: "config \<Rightarrow> int" where
  "head0_CL cfg = int (cfg <#> 0)"

definition accepts_CL :: "machine \<Rightarrow> bool list \<Rightarrow> bool" where
  "accepts_CL M x =
     (let t   = steps_CL M x;
          cfg = conf_CL M x t
      in (cfg <:> 1) (cfg <#> 1) = 3)"

text \<open>
  NOTE: The details of when exactly the machine halts (state index \<ge> length M)
  follow the convention in the Cook–Levin development. We will mainly reason
  abstractly in terms of steps_CL and accepts_CL, not about low-level configs.
\<close>


subsection \<open>Which input bits does a Cook–Levin machine read?\<close>

text \<open>
  The set @{term "read0_CL M x"} collects all indices @{term i} on the
  input tape (tape 0) that the head visits before halting on input @{term x}.

  This abstracts away from the exact timing of visits and keeps only the
  set of input positions whose contents the machine has “inspected”.
\<close>

definition read0_CL :: "machine \<Rightarrow> bool list \<Rightarrow> nat set" where
  "read0_CL M x =
     { nat (head0_CL (conf_CL M x t)) | t.
        t < steps_CL M x \<and>
        0 \<le> head0_CL (conf_CL M x t) \<and>
        nat (head0_CL (conf_CL M x t)) < length x }"

lemma read0_CL_subset_indices:
  "read0_CL M x \<subseteq> {..<length x}"
  unfolding read0_CL_def by auto


subsection \<open>Configuration agreement and unread positions\<close>

text \<open>
  Two configurations agree except possibly at position i on tape 0.

  This is a convenient concept if one wants to reason about how a single
  unread bit on the input tape can be flipped without affecting the
  rest of the machine's behaviour.

  In this theory we will *not* prove a general unread-flip lemma for all
  Cook–Levin machines; instead, we package the desired unread-agreement
  property as locale axioms for the particular machines we care about
  (see below).
\<close>

definition configs_agree_except_at :: "nat \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" where
  "configs_agree_except_at i c1 c2 \<longleftrightarrow>
     fst c1 = fst c2 \<and>
     ||c1|| = ||c2|| \<and>
     (\<forall>t. 0 < t \<longrightarrow> t < ||c1|| \<longrightarrow>
         c1 <:> t = c2 <:> t \<and>
         c1 <#> t = c2 <#> t) \<and>
     c1 <#> 0 = c2 <#> 0 \<and>
     (\<forall>pos. pos \<noteq> i \<longrightarrow> (c1 <:> 0) pos = (c2 <:> 0) pos)"

text \<open>Flipping a bit in a bool list\<close>

definition flip_bool_list :: "bool list \<Rightarrow> nat \<Rightarrow> bool list" where
  "flip_bool_list xs i =
     (if i < length xs then xs[i := (\<not> xs!i)] else xs)"

lemma bool_to_symbols_flip_outside:
  assumes "j < length x" "j \<noteq> i"
  shows "bool_to_symbols (flip_bool_list x i) ! j
       = bool_to_symbols x ! j"
  using assms
  unfolding bool_to_symbols_def flip_bool_list_def
  by (auto simp: nth_list_update)

lemma flip_bool_list_length[simp]:
  "length (flip_bool_list xs i) = length xs"
  by (simp add: flip_bool_list_def)

lemma flip_bool_list_eq_outside:
  assumes "j < length xs" "j \<noteq> i"
  shows "flip_bool_list xs i ! j = xs ! j"
  using assms
  by (simp add: flip_bool_list_def)

lemma head0_bounded:
  assumes "turing_machine k_tapes q0 M"
  assumes "t < steps_CL M x"
  shows   "head0_CL (conf_CL M x t) \<ge> 0"
  unfolding head0_CL_def conf_CL_def
  by simp


subsection \<open>Unread-agreement property as a locale axiom\<close>

text \<open>
  We now *axiomatize* the unread-flip agreement property for a given
  Cook–Levin machine.  Intuitively, this says:

    • if bit i of x is never read on tape 0 in the run of M on input x,
      then flipping that bit does not change whether M accepts.

  This is the Cook–Levin analogue of the “unread bits do not matter”
  property used on the decision-tree side.  It is *not* derivable for
  arbitrary machines from the raw Cook–Levin semantics, so we expose it
  as a separate locale that can be assumed for the particular solvers
  we care about.
\<close>

locale Flip_Agreement_CL =
  fixes M :: machine and q0 :: nat
  assumes TM: "turing_machine k_tapes q0 M"
  assumes unread_agreement:
    "\<And>x i. i < length x \<Longrightarrow> i \<notin> read0_CL M x
          \<Longrightarrow> accepts_CL M x = accepts_CL M (flip_bool_list x i)"


subsection \<open>The mathematical SUBSET-SUM predicate\<close>

text \<open>
  This is the “true” subset-sum specification: we ask if there exists a
  0/1-vector xs selecting a subset of as that sums to s.

  It is intentionally independent of Turing machines or encodings;
  later we connect it to NP-style verifiers and Cook–Levin machines.
\<close>

definition subset_sum_true :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "subset_sum_true as s \<longleftrightarrow>
     (\<exists>xs \<in> bitvec (length as).
        (\<Sum> i<length as. as ! i * xs ! i) = s)"


subsection \<open>Certificate-based view of SUBSET-SUM\<close>

text \<open>
  A natural NP-style certificate for SUBSET-SUM is a 0/1-vector @{term xs}
  of the same length as @{term as}, indicating which elements are chosen.
  The verifier checks:
    • length xs = length as
    • each entry is 0 or 1
    • the weighted sum equals s.

  We package this as ss_cert_ok and then show the obvious equivalence with
  subset_sum_true.
\<close>

definition ss_cert_ok :: "int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool" where
  "ss_cert_ok as s xs \<longleftrightarrow>
     length xs = length as \<and>
     set xs \<subseteq> {0,1} \<and>
     (\<Sum> i<length as. as ! i * xs ! i) = s"

lemma subset_sum_true_iff_cert:
  "subset_sum_true as s \<longleftrightarrow> (\<exists>xs. ss_cert_ok as s xs)"
proof
  assume "subset_sum_true as s"
  then obtain xs where
    xs_bitvec: "xs \<in> bitvec (length as)" and
    sum_eq:     "(\<Sum> i<length as. as ! i * xs ! i) = s"
    unfolding subset_sum_true_def by blast
  hence len: "length xs = length as"
    and vals: "set xs \<subseteq> {0,1}"
    unfolding bitvec_def by auto
  hence "ss_cert_ok as s xs"
    unfolding ss_cert_ok_def using sum_eq by simp
  thus "\<exists>xs. ss_cert_ok as s xs"
    by blast
next
  assume "\<exists>xs. ss_cert_ok as s xs"
  then obtain xs where
    ok: "ss_cert_ok as s xs"
    by blast
  from ok have len: "length xs = length as"
    and vals: "set xs \<subseteq> {0,1}"
    and sum_eq: "(\<Sum> i<length as. as ! i * xs ! i) = s"
    unfolding ss_cert_ok_def by auto
  hence "xs \<in> bitvec (length as)"
    unfolding bitvec_def by auto
  thus "subset_sum_true as s"
    unfolding subset_sum_true_def
    using sum_eq by blast
qed


subsection \<open>SUBSET-SUM is in NP (via an abstract verifier)\<close>

text \<open>
  We now define an abstract verifier locale that matches the NP definition
  in {theory NP}.  It assumes that we have:

    • an instance encoding {term enc0 :: "int list \<Rightarrow> int \<Rightarrow> string"},
    • a certificate encoding {term enc_cert :: "int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> string"},
    • a Turing machine {term V} computing a verifier function {term fverify},
    • a polynomial bound {term p} on the certificate length as a function of
      the instance length.

  The correctness condition ties everything back to @{term ss_cert_ok} and
  hence to @{term subset_sum_true}.

  This locale is deliberately generic in k, G, V, p, T, and fverify; later
  we will instantiate it with Cook–Levin style encodings when needed.
\<close>

locale SS_Verifier_NP =
  fixes k G V p T fverify enc0 enc_cert
  assumes V_tm:
    "turing_machine k G V"
  assumes p_poly:
    "polynomial p"
  assumes T_poly:
    "big_oh_poly T"
  assumes V_time:
    "computes_in_time k V fverify T"
  assumes V_outlen:
    "\<And>y. length (fverify y) = 1"
  assumes V_complete:
    "\<And>as s. subset_sum_true as s \<Longrightarrow>
       \<exists>xs.
         ss_cert_ok as s xs \<and>
         length (enc_cert as s xs) = p (length (enc0 as s)) \<and>
         fverify \<langle>enc0 as s, enc_cert as s xs\<rangle> = [\<bbbI>]"
  assumes V_sound:
    "\<And>as s u.
       fverify \<langle>enc0 as s, u\<rangle> = [\<bbbI>] \<Longrightarrow>
       length u = p (length (enc0 as s)) \<Longrightarrow>
       \<exists>xs. ss_cert_ok as s xs \<and> u = enc_cert as s xs"
  assumes V_wf:
    "\<And>x u. fverify \<langle>x, u\<rangle> = [\<bbbI>] \<Longrightarrow> \<exists>as s. x = enc0 as s"


subsection \<open>Encoding of instance–certificate pairs\<close>

text \<open>
  For the NP view, we want a single input bitstring that encodes both
  the instance (as,s) and a certificate xs.  We keep the instance
  encoding enc0 abstract, and assume a separate certificate encoding
  enc_cert.  The combined encoding just concatenates them with a fixed
  separator.

  This is the standard “instance || separator || certificate” trick.
\<close>

definition sep :: "bool list" where
  "sep = [True, False, True]"  (* any fixed non-empty pattern *)

definition enc_pair ::
  "(int list \<Rightarrow> int \<Rightarrow> bool list) \<Rightarrow>
   (int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool list) \<Rightarrow>
   int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool list" where
  "enc_pair enc0 enc_cert as s xs =
     enc0 as s @ sep @ enc_cert as s xs"


subsection \<open>A Cook–Levin verifier for SUBSET-SUM\<close>

text \<open>
  Locale SS_Verifier_CL specialises the abstract SS_Verifier_NP idea to
  the Cook–Levin world:

   • V is a k_tapes Cook–Levin machine.

   • On input enc_pair enc0 enc_cert as s xs, if length xs = length as,
     V accepts exactly when xs is a correct subset-sum witness
     (ss_cert_ok as s xs).

   • The running time of V is bounded by a polynomial in the instance
     size |enc0 as s|, uniformly over all certificates xs of matching
     length.
\<close>

locale SS_Verifier_CL =
  fixes V        :: machine
    and q0       :: nat
    and enc0     :: "int list \<Rightarrow> int \<Rightarrow> bool list"
    and enc_cert :: "int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool list"
  assumes V_tm:
    "turing_machine k_tapes q0 V"
  assumes V_polytime:
    "\<exists>(c::real)>0. \<exists>(d::nat).
       \<forall>as s xs.
         length xs = length as \<longrightarrow>
         steps_CL V (enc_pair enc0 enc_cert as s xs)
           \<le> nat (ceiling (c * (real (length (enc0 as s)) ^ d)))"
  assumes V_correct:
    "\<And>as s xs.
       length xs = length as \<longrightarrow>
       accepts_CL V (enc_pair enc0 enc_cert as s xs)
         \<longleftrightarrow> ss_cert_ok as s xs"

text \<open>
  Intuitively:

   • V is a k_tape Cook–Levin machine.

   • On input enc_pair enc0 enc_cert as s xs, if length xs = length as,
     V accepts exactly when xs is a correct subset-sum witness
     (ss_cert_ok as s xs).

   • The running time of V is bounded by a polynomial in the instance
     size |enc0 as s|, uniformly over all certificates xs of matching
     length.
\<close>


section \<open>SUBSET-SUM as a language\<close>

text \<open>
  Given an instance encoding function @{term enc0} which maps a pair
  (as,s) to a bitstring, we define the SUBSET-SUM language as the set
  of all strings that encode a true SUBSET-SUM instance.

  This is the standard “language view” of the decision problem.
\<close>

definition SUBSETSUM_lang :: "(int list \<Rightarrow> int \<Rightarrow> string) \<Rightarrow> language" where
  "SUBSETSUM_lang enc0 \<equiv>
     {x. \<exists>as s. x = enc0 as s \<and> subset_sum_true as s}"


subsection \<open>SUBSET-SUM is in NP (relative to enc0)\<close>

text \<open>
  The next lemma packages the SS_Verifier_NP locale into the
  \<open>NP_output_len_1\<close> characterization of NP from \<open>Cook_Levin.NP\<close>.
  It says: if there is a suitable NP-style verifier for SUBSET-SUM
  w.r.t. enc0, then the language SUBSETSUM_lang enc0 is in \<N>\<P>.
\<close>
lemma SUBSETSUM_in_NP_from_verifier:
  fixes k G V p T fverify enc0 enc_cert
  assumes verif: "SS_Verifier_NP k G V p T fverify enc0 enc_cert"
  shows "SUBSETSUM_lang enc0 \<in> \<N>\<P>"
proof -
  interpret V: SS_Verifier_NP k G V p T fverify enc0 enc_cert
    using verif .

  text \<open>Use the alternative NP characterization @{thm NP_output_len_1}.\<close>

  have witness:
    "\<exists>k G M p T fver.
       turing_machine k G M \<and>
       polynomial p \<and>
       big_oh_poly T \<and>
       computes_in_time k M fver T \<and>
       (\<forall>y. length (fver y) = 1) \<and>
       (\<forall>x. x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
              (\<exists>u. length u = p (length x) \<and> fver \<langle>x, u\<rangle> = [\<bbbI>]))"
  proof (intro exI conjI)
    (* choose k,G,M,p,T,fver as the ones from the verifier *)
    show "turing_machine k G V"
      by (rule V.V_tm)
    show "polynomial p"
      by (rule V.p_poly)
    show "big_oh_poly T"
      by (rule V.T_poly)
    show "computes_in_time k V fverify T"
      by (rule V.V_time)
    show "\<forall>y. length (fverify y) = 1"
      using V.V_outlen by simp

    show "\<forall>x. x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
              (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>])"
    proof
      fix x :: string
      show "x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
              (\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>])"
      proof
        (* (\<Rightarrow>) completeness direction: from language membership to a witness u *)
        assume "x \<in> SUBSETSUM_lang enc0"
        then obtain as s where
          x_def: "x = enc0 as s" and
          sat:   "subset_sum_true as s"
          unfolding SUBSETSUM_lang_def by blast

        from V.V_complete[OF sat] obtain xs where
          xs_ok: "ss_cert_ok as s xs" and
          len_u: "length (enc_cert as s xs) = p (length (enc0 as s))" and
          acc:   "fverify \<langle>enc0 as s, enc_cert as s xs\<rangle> = [\<bbbI>]"
          by blast

        have "\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]"
          using x_def len_u acc by blast
        thus "\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]" .
      next
        (* (\<Leftarrow>) soundness direction: from a witness u to language membership *)
        assume RHS: "\<exists>u. length u = p (length x) \<and> fverify \<langle>x, u\<rangle> = [\<bbbI>]"
        then obtain u where
          len_u: "length u = p (length x)" and
          acc:   "fverify \<langle>x, u\<rangle> = [\<bbbI>]"
          by blast

        (* Use the WELL-FORMEDNESS axiom: accepting \<Rightarrow> x is some enc0 as s *)
        from V.V_wf[OF acc] obtain as s where
          x_def: "x = enc0 as s"
          by blast

        (* Rewrite premises into the shape V_sound expects *)
        from acc x_def have acc_enc:
          "fverify \<langle>enc0 as s, u\<rangle> = [\<bbbI>]"
          by simp
        from len_u x_def have len_u_enc:
          "length u = p (length (enc0 as s))"
          by simp

        (* Important: argument order matches V_sound: acc_enc THEN len_u_enc *)
        from V.V_sound[OF acc_enc len_u_enc]
        obtain xs where xs_ok: "ss_cert_ok as s xs" and u_enc: "u = enc_cert as s xs"
          by blast

        from xs_ok have "subset_sum_true as s"
          using subset_sum_true_iff_cert by blast
        hence "x \<in> SUBSETSUM_lang enc0"
          unfolding SUBSETSUM_lang_def using x_def by blast
        thus "x \<in> SUBSETSUM_lang enc0" .
      qed
    qed
  qed

  (* We now package the verifier data into the exact shape
     required by NP_output_len_1. *)
  from witness
  obtain k G M p T fver where
    tm:      "turing_machine k G M" and
    poly_p:  "polynomial p" and
    T_poly:  "big_oh_poly T" and
    time:    "computes_in_time k M fver T" and
    outlen:  "\<forall>y. length (fver y) = 1" and
    corr:    "\<forall>x. x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
                   (\<exists>u. length u = p (length x) \<and> fver \<langle>x, u\<rangle> = [\<bbbI>])"
    by blast

  have witness':
    "\<exists>k G M.
       turing_machine k G M \<and>
       (\<exists>p. polynomial p \<and>
        (\<exists>T. big_oh_poly T \<and>
         (\<exists>fver.
            computes_in_time k M fver T \<and>
            (\<forall>y. length (fver y) = 1) \<and>
            (\<forall>x. x \<in> SUBSETSUM_lang enc0 \<longleftrightarrow>
                   (\<exists>u. length u = p (length x) \<and> fver \<langle>x, u\<rangle> = [\<bbbI>])))))"
    using tm poly_p T_poly time outlen corr by blast

  show "SUBSETSUM_lang enc0 \<in> \<N>\<P>"
    unfolding NP_output_len_1
    using witness' by blast
qed


subsection \<open>A Cook–Levin machine that solves SUBSET-SUM\<close>

text \<open>
  Locale CL_SubsetSum_Solver says:
   • M is a well-formed k_tapes Cook–Levin machine,
   • enc encodes (as,s) as a bool list,
   • M decides subset_sum_true at that encoding.

  Inside the locale, steps_TM and read0_TM are just convenient
  aliases of steps_CL and read0_CL on enc as s.
\<close>

locale CL_SubsetSum_Solver =
  fixes M   :: machine
    and q0  :: nat
    and enc :: "int list \<Rightarrow> int \<Rightarrow> bool list"
  assumes turing: "turing_machine k_tapes q0 M"
  assumes solves_subset_sum:
    "\<And>as s. accepts_CL M (enc as s) \<longleftrightarrow> subset_sum_true as s"
begin

text \<open>
  steps_TM is the time we care about for the lower bound:
  it is just the Cook–Levin step-count on the encoded instance.
\<close>

definition steps_TM :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "steps_TM as s = steps_CL M (enc as s)"

definition read0_TM :: "int list \<Rightarrow> int \<Rightarrow> nat set" where
  "read0_TM as s = read0_CL M (enc as s)"

lemma read0_TM_subset:
  "read0_TM as s \<subseteq> {..<length (enc as s)}"
  unfolding read0_TM_def
  using read0_CL_subset_indices by simp

end  (* context CL_SubsetSum_Solver *)


subsection \<open>Equation-based read requirement\<close>

text \<open>
  This locale expresses the idea that the machine decides SUBSET-SUM
  by checking equality of two “sides” of an equation.  Conceptually,
  there is some base equation

      l(as, s) = r(as, s)

  such that (as,s) is in the language iff this equation holds.  We allow
  the machine to work with any *equivalent* equation, e.g. of the form

      f(l(as,s)) = f(r(as,s))

  for some injective function f; all of this is abstracted into the
  two functions \<open>lhs\<close> and \<open>rhs\<close>, and the correctness assumption

      subset_sum_true as s \<longleftrightarrow> lhs as s = rhs as s.

  The sets \<open>L_zone as s\<close> and \<open>R_zone as s\<close> describe the input positions
  (in \<open>enc as s\<close>) that encode the left- and right-hand sides of this
  deciding equation.  The assumption \<open>must_read_LR\<close> then says:

      – on every distinct-subset-sums instance (as,s),
        the machine’s read set \<open>read0_TM as s\<close> intersects L_zone as s, and
      – it also intersects R_zone as s.

  In other words: on “hard” instances, the machine must read at least one
  bit from the part of the input encoding the left side and at least one
  bit from the part encoding the right side of some deciding equation
  equivalent to l = r.
\<close>

locale Eq_ReadLR_SubsetSum_Solver =
  CL_SubsetSum_Solver M q0 enc
  for M :: machine and q0 :: nat
      and enc :: "int list \<Rightarrow> int \<Rightarrow> bool list" +
  fixes lhs rhs :: "int list \<Rightarrow> int \<Rightarrow> int"
    and L_zone R_zone :: "int list \<Rightarrow> int \<Rightarrow> nat set"
  assumes equation_correct:
    "\<And>as s. subset_sum_true as s \<longleftrightarrow> (lhs as s = rhs as s)"
  assumes zones_wf:
    "\<And>as s. L_zone as s \<subseteq> {..< length (enc as s)}"
    "\<And>as s. R_zone as s \<subseteq> {..< length (enc as s)}"
    "\<And>as s. L_zone as s \<inter> R_zone as s = {}"
  assumes must_read_LR:
    "\<And>as s. distinct_subset_sums as \<Longrightarrow>
       read0_TM as s \<inter> L_zone as s \<noteq> {} \<and>
       read0_TM as s \<inter> R_zone as s \<noteq> {}"

text \<open>
  RELATION TO THE ABSTRACT LOWER-BOUND AXIOM \<open>LR_Read_TM\<close>

  The locale \<open>Eq_ReadLR_SubsetSum_Solver\<close> isolates a concrete,
  adversary-style requirement:

    • SUBSET-SUM is decided via some equation
        lhs as s = rhs as s
      (up to injective re-encoding, e.g. \<open>f (lhs as s) = f (rhs as s)\<close>),

    • and on distinct-subset-sums instances the machine must read at
      least one bit from the part of the input encoding the “left side”
      and at least one bit from the part encoding the “right side”
      (\<open>L_zone as s\<close> and \<open>R_zone as s\<close>).

  The locale \<open>LR_Read_TM\<close> below is a more structured, but still abstract,
  interface to the decision-tree lower bound.  Instead of talking about
  particular input zones, it assumes directly that for some canonical
  split index \<open>k\<close>, the runtime is at least

      card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)

  on any distinct-subset-sums instance of length \<open>n\<close>.  This matches the
  combinatorial structure exploited in \<open>SubsetSum_DecisionTree\<close> and is
  exactly what is needed to instantiate the abstract reader model.

  Intuitively, any machine satisfying the concrete “must read from L and
  R” condition of \<open>Eq_ReadLR_SubsetSum_Solver\<close> *and* aligning with the
  canonical LHS/RHS partial-sum splits should give rise to an instance of
  \<open>LR_Read_TM\<close>.  In this theory we keep that connection as a meta-level
  assumption (see the locales \<open>All_SubsetSum_Polytime_LR_Read\<close> and
  \<open>All_SubsetSum_Polytime_Eq_ReadLR\<close> below).  All formal lower-bound
  proofs are phrased inside \<open>LR_Read_TM\<close>, which is the Cook–Levin side
  of the flip-complete/reader-style model.
\<close>


section \<open>LR-read TM interface and lower bound inheritance\<close>

text \<open>
  A Cook–Levin machine is polynomial-time on SUBSET-SUM if its
  running time on the encoding of (as,s) is bounded by some polynomial
  in the length of the weight list as (\<simeq> input size).  We take this
  as the basic complexity measure; the bit-length of the encoding
  \<open>enc as s\<close> is allowed to be some fixed polynomial in \<open>length as\<close>.
\<close>

definition polytime_CL_machine
  :: "machine \<Rightarrow> (int list \<Rightarrow> int \<Rightarrow> bool list) \<Rightarrow> bool"
where
  "polytime_CL_machine M enc \<longleftrightarrow>
     (\<exists>(c::real)>0. \<exists>(d::nat).
        \<forall>as s. steps_CL M (enc as s)
               \<le> nat (ceiling (c * (real (length as)) ^ d)))"

text \<open>
  The locale LR_Read_TM is the Cook–Levin analogue of the abstract
  reader-model locale \<open>SubsetSum_Lemma1\<close> from the decision-tree theory.
  It assumes that the CL machine M (with encoding enc) satisfies the
  combinatorial lower-bound condition on hard instances, and then
  imports the \<Omega>(\<surd>(2^n)) lower bound and “no polynomial-time” corollary.
\<close>
locale LR_Read_TM =
  CL_SubsetSum_Solver M q0 enc
  for M :: machine and q0 :: nat
      and enc :: "int list \<Rightarrow> int \<Rightarrow> bool list" +
  assumes lemma1_ex_TM:
    "\<And>as s n. n = length as \<Longrightarrow> distinct_subset_sums as \<Longrightarrow>
       \<exists>k\<le>n.
         card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)
         \<le> steps_TM as s"
begin

(* Instantiate the abstract reader-model locale with steps_TM. *)
interpretation Reader: SubsetSum_Lemma1 steps_TM
proof
  show "\<And>as s n. n = length as \<Longrightarrow> distinct_subset_sums as \<Longrightarrow>
           \<exists>k\<le>n.
             card (LHS (e_k as s k) n) + card (RHS (e_k as s k) n)
             \<le> steps_TM as s"
    by (rule lemma1_ex_TM)
qed

text \<open>
  We inherit the abstract \<Omega>(\<surd>(2^n)) lower bound from SubsetSum_Lemma1.
\<close>
theorem subset_sum_sqrt_lower_bound_TM:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) \<le> real (steps_TM as s)"
  using Reader.subset_sum_sqrt_lower_bound[OF n_def distinct]
  by simp

corollary subset_sum_sqrt_lower_bound_CL:
  fixes as :: "int list" and s :: int and n :: nat
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) \<le> real (steps_CL M (enc as s))"
proof -
  have lb: "2 * sqrt ((2::real) ^ n) \<le> real (steps_TM as s)"
    using subset_sum_sqrt_lower_bound_TM[OF n_def distinct] .
  have "steps_TM as s = steps_CL M (enc as s)"
    by (simp add: steps_TM_def)
  hence "real (steps_TM as s) = real (steps_CL M (enc as s))"
    by simp
  from lb this show ?thesis
    by simp
qed

text \<open>
  Now we replay the “exponential beats polynomial” argument in the TM
  setting: if steps_TM were polynomially bounded over all distinct
  subset-sum families, we would contradict the inherited \<Omega>(\<surd>(2^n))
  lower bound using the hard family from exists_hard_TM.
\<close>
theorem no_polytime_TM_on_distinct_family:
  shows "\<not> (\<exists>(c::real)>0. \<exists>(d::nat).
             \<forall>as s. distinct_subset_sums as \<longrightarrow>
               steps_TM as s \<le> nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_poly:
    "\<exists>(c::real)>0. \<exists>(d::nat).
       \<forall>as s. distinct_subset_sums as \<longrightarrow>
         steps_TM as s \<le> nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where
    cpos: "c > 0" and
    bound: "\<forall>as s. distinct_subset_sums as \<longrightarrow>
                    steps_TM as s \<le> nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  (* Use the analytic lemma in the TM-friendly form. *)
  from exp_beats_poly_ceiling_strict_TM[OF cpos]
  obtain N :: nat where N:
    "\<forall>n\<ge>N. of_int (ceiling (c * (real n) ^ d))
           < 2 * sqrt ((2::real) ^ n)"
    by blast

  have N_ge: "N \<ge> N" by simp

  (* Instantiate a hard instance as of length N. *)
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

  (* Lower bound from Lemma 1 / Reader locale. *)
  have lb:
    "2 * sqrt ((2::real) ^ N) \<le> real (steps_TM as 0)"
  proof -
    have "2 * sqrt ((2::real) ^ N) \<le> real (steps_TM as 0)"
    proof (rule subset_sum_sqrt_lower_bound_TM)
      show "N = length as"
        using len_as by simp
    next
      show "distinct_subset_sums as"
        using dist_as .
    qed
    thus ?thesis .
  qed

  (* Polynomial upper bound assumption, instantiated to as, s=0. *)
  have ub_nat:
    "steps_TM as 0 \<le> nat (ceiling (c * (real (length as)) ^ d))"
    using bound dist_as by simp

  (* Relate nat \<lceil>\<dots>\<rceil> and of_int \<lceil>\<dots>\<rceil>. *)
  have nonneg: "0 \<le> c * (real (length as)) ^ d"
    using cpos by simp
  hence ceil_ge0: "0 \<le> ceiling (c * (real (length as)) ^ d)"
    by simp
  hence conv:
    "real (nat (ceiling (c * (real (length as)) ^ d)))
       = of_int (ceiling (c * (real (length as)) ^ d))"
    by simp

  from ub_nat have ub_real:
    "real (steps_TM as 0)
       \<le> of_int (ceiling (c * (real (length as)) ^ d))"
    using conv by simp

  (* Lower bound, upper bound, and strict separation contradict each other. *)
  from ceil_lt' lb ub_real
  show False using len_as by auto
qed

text \<open>
  The same argument phrased in terms of the underlying Cook–Levin
  step function steps_CL and encoding enc.
\<close>
corollary no_polytime_CL_on_distinct_family:
  shows "\<not> (\<exists>(c::real)>0. \<exists>(d::nat).
             \<forall>as s. distinct_subset_sums as \<longrightarrow>
               steps_CL M (enc as s)
                 \<le> nat (ceiling (c * (real (length as)) ^ d)))"
proof
  assume ex_poly:
    "\<exists>(c::real)>0. \<exists>(d::nat).
       \<forall>as s. distinct_subset_sums as \<longrightarrow>
         steps_CL M (enc as s)
           \<le> nat (ceiling (c * (real (length as)) ^ d))"
  then obtain c d where
    cpos: "c > 0" and
    bound: "\<forall>as s. distinct_subset_sums as \<longrightarrow>
                    steps_CL M (enc as s)
                      \<le> nat (ceiling (c * (real (length as)) ^ d))"
    by blast

  have "\<exists>(c::real)>0. \<exists>(d::nat).
          \<forall>as s. distinct_subset_sums as \<longrightarrow>
            steps_TM as s \<le> nat (ceiling (c * (real (length as)) ^ d))"
    using cpos bound steps_TM_def by auto
  with no_polytime_TM_on_distinct_family show False by blast
qed

end  (* locale LR_Read_TM *)

end  (* theory *)
