theory SubsetSum_CookLevin
  imports
    "Cook_Levin.NP"
    "SubsetSum_DecisionTree"
begin

definition k_tapes :: nat where
  "k_tapes = 2"

definition bool_to_symbols :: "bool list ⇒ symbol list" where
  "bool_to_symbols bs = map (λb. if b then 3 else 2) bs"

definition steps_CL :: "machine ⇒ bool list ⇒ nat" where
  "steps_CL M x =
     (LEAST t. fst (execute M (start_config k_tapes (bool_to_symbols x)) t) ≥ length M)"

definition conf_CL :: "machine ⇒ bool list ⇒ nat ⇒ config" where
  "conf_CL M x t = execute M (start_config k_tapes (bool_to_symbols x)) t"

definition head0_CL :: "config ⇒ int" where
  "head0_CL cfg = int (cfg <#> 0)"

definition accepts_CL :: "machine ⇒ bool list ⇒ bool" where
  "accepts_CL M x =
     (let t = steps_CL M x;
          cfg = conf_CL M x t
      in (cfg <:> 1) (cfg <#> 1) = 3)"

definition stepf_CL_for :: "machine ⇒ config ⇒ bool ⇒ config" where
  "stepf_CL_for M cfg b = exe M cfg"

definition final_acc_CL :: "config ⇒ bool" where
  "final_acc_CL cfg = ((cfg <:> 1) (cfg <#> 1) = 3)"

lemma step_sem_CL:
  "conf_CL M x (Suc t) =
     stepf_CL_for M (conf_CL M x t)
       (x ! nat (head0_CL (conf_CL M x t)))"
  unfolding conf_CL_def stepf_CL_for_def head0_CL_def
  by simp

definition read0_CL :: "machine ⇒ bool list ⇒ nat set" where
  "read0_CL M x =
     { i. ∃t < steps_CL M x.
            nat (head0_CL (conf_CL M x t)) = i }"

lemma unread_agree_CL:
  assumes agree:  "⋀i. i ∈ read0_CL M x ⟹ x ! i = y ! i"
  shows   "steps_CL M x = steps_CL M y"
      and "accepts_CL M x = accepts_CL M y"
      and "read0_CL M x = read0_CL M y"
  sorry

lemma steps_ge_read0_CL:
  "card (read0_CL M x) ≤ steps_CL M x"
  sorry

locale SubsetSum_CookLevin =
  fixes M :: machine
    and encode_instance :: "int list ⇒ int ⇒ bool list"
  assumes solves_subset_sum:
    "⋀as s. distinct_subset_sums as ⟹
       accepts_CL M (encode_instance as s) ⟷
       (∃xs∈bitvec (length as). (∑ i<length as. as ! i * xs ! i) = s)"
begin

definition steps :: "int list ⇒ int ⇒ nat" where
  "steps as s = steps_CL M (encode_instance as s)"

definition seenL :: "int list ⇒ int ⇒ nat ⇒ int set" where
  "seenL as s k = undefined"

definition seenR :: "int list ⇒ int ⇒ nat ⇒ int set" where
  "seenR as s k = undefined"

lemma coverage_ex:
  "⋀as s. distinct_subset_sums as ⟹
     ∃k≤length as.
       seenL as s k = LHS (e_k as s k) (length as) ∧
       seenR as s k = RHS (e_k as s k) (length as)"
  sorry

lemma steps_lb:
  "⋀as s k. steps as s ≥ card (seenL as s k) + card (seenR as s k)"
  sorry

interpretation SubsetSum_Reader_NoK steps seenL seenR
proof
  show "⋀as s. distinct_subset_sums as ⟹
          ∃k≤length as.
            seenL as s k = LHS (e_k as s k) (length as) ∧
            seenR as s k = RHS (e_k as s k) (length as)"
    by (rule coverage_ex)
next
  show "⋀as s k. steps as s ≥ card (seenL as s k) + card (seenR as s k)"
    by (rule steps_lb)
qed

theorem subset_sum_sqrt_lower_bound_TM:
  fixes as :: "int list" and s :: int and n :: nat
  assumes "n = length as" "distinct_subset_sums as"
  shows "2 * sqrt ((2::real) ^ n) ≤ real (steps as s)"
  by (simp add: assms(1,2) subset_sum_sqrt_lower_bound)

end  (* locale SubsetSum_CookLevin *)

end
