(*:maxLineLen=78:*)

theory Highway
  imports 
    Main
    "HOL-Lattice.Orders"
    HOL.Rat
begin

sledgehammer_params [smt_proofs = false]

section \<open>Axiomatization\<close>

text \<open> Isabelle/HOL will not let us have a function 
   \<open>weight ::validator \<Rightarrow> rat\<close> in a type class because it is missing a 
   parameter. We use phantom parameters to get around this. \<close>

datatype 'a validator = validator nat
datatype 'a vote_option = vote_for nat | abstain ("\<emptyset>")

class highway = partial_order +
  fixes vote_value :: "'a \<Rightarrow> 'a vote_option"
  fixes sender :: "'a \<Rightarrow> 'a validator"
  fixes weight :: "'a validator \<Rightarrow> rat"
  assumes non_neg_weights: "weight v \<ge> 0"

section \<open>Consistency\<close>

text \<open> \<^emph>\<open> This is an elementary consistency proof, however it will be 
          desirable to have model more complex sets of assumptions \<close> \<close>

datatype example = example

instantiation example :: highway
begin
fun leq_example :: "example \<Rightarrow> example \<Rightarrow> bool" where
  "example \<sqsubseteq> example = True"

definition vote_value_example :: "example \<Rightarrow> example vote_option" where
  "vote_value_example m = vote_for 0"
definition sender_example :: "example \<Rightarrow> example validator" where
  "sender_example m = validator 0"
definition weight_example :: "example validator \<Rightarrow> rat" where
  "weight_example v = 1"

instance
  apply (standard) 
    apply (metis (full_types) example.exhaust leq_example.simps)
    apply (metis (full_types) example.exhaust)
    apply (metis (full_types) example.exhaust)
    apply (simp add: weight_example_def)
  done
end

section \<open>Equivocations\<close>

definition (in highway) 
  equivocation :: "'a validator \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "equivocation v x y \<equiv> 
       v = sender x \<and> v = sender y \<and> \<not> (x \<sqsubseteq> y) \<and> \<not> (y \<sqsubseteq> x)"

lemma (in highway) equivocation_neg:
  assumes "v = sender x" and "v = sender y"
  shows "\<not> equivocation v x y \<equiv> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  using assms equivocation_def by auto

abbreviation (in partial_order) downset :: "'a set \<Rightarrow> 'a set" ("\<down>") where
  "\<down> S \<equiv> { m . \<exists> s \<in> S. m \<sqsubseteq> s }"

lemma (in partial_order) downset_universe:
  "\<down> (UNIV :: 'a set) = UNIV"
  using leq_refl 
  by fastforce

definition (in highway)
  byzantine_in :: "'a set \<Rightarrow> 'a validator \<Rightarrow> bool" where
  "byzantine_in S v \<equiv> \<exists> x \<in> \<down> S. \<exists> y \<in> \<down> S. equivocation v x y"

definition (in highway) byzantine :: "'a validator \<Rightarrow> bool" where
  "byzantine v \<equiv> byzantine_in UNIV v"

lemma byzantine_def':
  "byzantine v = (\<exists> x y. equivocation v x y)"
  unfolding byzantine_def byzantine_in_def
  by (metis (mono_tags, lifting) UNIV_I downset_universe)

definition (in highway) 
  honest_message_weight :: "'a set \<Rightarrow> 'a set \<Rightarrow> rat" ("weight\<^sub>\<M>") where
  "weight\<^sub>\<M> S T = 
     (\<Sum> v | (\<exists> s \<in> T . v = sender s) 
                 \<and> weight v \<noteq> 0
                 \<and> \<not> byzantine_in S v
                 . weight v)"

lemma (in highway) messages_weight_mono:
  assumes 
    "T \<subseteq> U" 
    "finite {v. \<exists> s \<in> U. v = sender s \<and> weight v \<noteq> 0 \<and> \<not> byzantine_in S v}"
  shows "weight\<^sub>\<M> S T \<le> weight\<^sub>\<M> S U"
proof -
  have "{v. \<exists> s \<in> T. v = sender s \<and> weight v \<noteq> 0 \<and> \<not> byzantine_in S v} 
          \<subseteq> {v. \<exists> s \<in> U. v = sender s \<and> weight v \<noteq> 0 \<and> \<not> byzantine_in S v}"
    using assms(1)
    by blast
  with assms(2) show ?thesis
    unfolding honest_message_weight_def
    by (simp add: non_neg_weights sum_mono2)
qed 

definition (in highway) 
  most_recent_for :: "'a validator \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "most_recent_for v S = 
     { s \<in> S . v = sender s 
        \<and> (\<forall> t \<in> S. v = sender t \<longrightarrow> s \<sqsubseteq> t \<longrightarrow> s = t) }"

lemma (in highway) most_recent_for_idem:
  "most_recent_for v (most_recent_for v S) = most_recent_for v S"
  unfolding most_recent_for_def by fastforce

fun (in partial_order) descending_chain_list :: "'a list \<Rightarrow> bool" where
  "descending_chain_list [] = True"
| "descending_chain_list [x] = True"
| "descending_chain_list (x1 # x2 # xs) 
     = (x2 \<sqsubseteq> x1 \<and> x2 \<noteq> x1 \<and> descending_chain_list (x2 # xs))"

lemma (in partial_order) descending_chain_list_drop_penultimate:
  "descending_chain_list (x1 # x2 # xs) \<Longrightarrow> descending_chain_list (x1 # xs)"
  by (induct xs, 
        simp, 
        metis descending_chain_list.simps(3) leq_antisym leq_trans)

lemma (in partial_order) descending_chain_list_greater_than_others:
  assumes "descending_chain_list (x # xs)"
  shows "\<forall> y \<in> set xs . y \<sqsubseteq> x \<and> y \<noteq> x"
  using assms descending_chain_list_drop_penultimate
  by (induct xs, fastforce+)

lemma (in partial_order) descending_chain_list_distinct:
  "descending_chain_list xs \<Longrightarrow> distinct xs"
  by (induct xs, 
        simp, 
        metis 
          distinct.simps(2) 
          descending_chain_list.elims(3) 
          descending_chain_list.simps(3) 
          descending_chain_list_greater_than_others)

lemma (in highway) most_recent_exists:
  assumes "finite S" "m \<in> S" "v = sender m"
  shows "\<exists> n \<in> most_recent_for v S . m \<sqsubseteq> n"
proof (rule ccontr)
  assume "\<not> (\<exists> n \<in> most_recent_for v S . m \<sqsubseteq> n)"
  hence fresh: 
    "\<forall> n \<in> S. m \<sqsubseteq> n 
        \<longrightarrow> v = sender n 
        \<longrightarrow> (\<exists> p \<in> S. v = sender p \<and> n \<noteq> p \<and> m \<sqsubseteq> n \<and> n \<sqsubseteq> p)"
    using most_recent_for_def by auto
  {
    fix n :: nat
    have "\<exists> xs . 
            descending_chain_list xs 
            \<and> length xs = n 
            \<and> set xs \<subseteq> S
            \<and> (\<forall> x \<in> set xs. v = sender x \<and> m \<sqsubseteq> x)"
    proof (induct n)
      case 0
      then show ?case
        by simp 
    next
      case (Suc n)
      then show ?case
      proof (cases "n = 0")
        assume "n = 0"
        have 
          "descending_chain_list [m]" 
          "length [m] = Suc 0" 
          "set [m] \<subseteq> S"
          "\<forall> x \<in> set [m] . v = sender x \<and> m \<sqsubseteq> x"
          using assms leq_refl
          by auto  
        thus ?case 
          unfolding \<open>n = 0\<close>
          by blast
      next
        assume 
          "n \<noteq> 0"
          "\<exists>xs.  
             descending_chain_list xs 
             \<and> length xs = n 
             \<and> set xs \<subseteq> S 
             \<and> (\<forall>x\<in>set xs. v = sender x \<and> m \<sqsubseteq> x)"
        from this obtain x xs where
            "descending_chain_list (x # xs)"
            "length (x # xs) = n"
            "set (x # xs) \<subseteq> S"
            "\<forall> x' \<in> set (x # xs). v = sender x' \<and> m \<sqsubseteq> x'"
            "m \<sqsubseteq> x"
          by (metis 
                (no_types, lifting) 
                length_0_conv 
                length_greater_0_conv 
                descending_chain_list.elims(2) 
                nth_Cons_0 nth_mem)
        moreover from this obtain y where
            "y \<in> S"
            "v = sender y"
            "y \<noteq> x"
            "x \<sqsubseteq> y"
            "m \<sqsubseteq> y"
          by (metis fresh list.set_intros(1) leq_trans subset_eq)
        ultimately have
            "descending_chain_list (y # x # xs)"
            "length (y # x # xs) = Suc n"
            "set (y # x # xs) \<subseteq> S"
            "\<forall> x' \<in> set (y # x # xs). v = sender x' \<and> m \<sqsubseteq> x'"
          by auto
        thus ?case by blast
      qed 
    qed
  }
  from this obtain xs :: "'a list" where
    "descending_chain_list xs"
    "length xs = card S + 1"
    "set xs \<subseteq> S"
    by blast
  with \<open>finite S\<close> \<open>descending_chain_list xs\<close> \<open>set xs \<subseteq> S\<close>
  have "length xs \<le> card S"
    by (metis card_mono distinct_card descending_chain_list_distinct)
  with \<open>length xs = card S + 1\<close> show False
    by linarith
qed

lemma (in highway) non_byzantine_most_recent_for:
  assumes "\<not> byzantine_in S v"
      and "m \<in> most_recent_for v S"
      and "n \<in> most_recent_for v S"
    shows "m = n"
proof -
  have "m \<in> S" "n \<in> S" "v = sender m" "v = sender n"
    using assms most_recent_for_def by auto
  moreover with assms(1) have "m \<sqsubseteq> n \<or> n \<sqsubseteq> m"
    unfolding byzantine_in_def equivocation_def
    using leq_refl by blast
  ultimately show ?thesis
    using assms(2) assms(3) most_recent_for_def by force
qed

lemma (in highway) most_recent_exists_unique:
  assumes 
    "finite S" 
    "\<not> byzantine_in S v" 
    "m \<in> S" 
    "v = sender m"
  shows "\<exists>! n \<in> most_recent_for v S . m \<sqsubseteq> n"
proof (rule ccontr)
  assume "\<not> (\<exists>! n . n \<in> most_recent_for v S \<and> m \<sqsubseteq> n)"
  moreover have "\<exists> n. n \<in> most_recent_for v S \<and> m \<sqsubseteq> n"
    using assms(1) assms(3) assms(4) most_recent_exists by blast
  ultimately obtain p q where
    "p \<in> most_recent_for v S"
    "q \<in> most_recent_for v S"
    "p \<noteq> q"
    by blast
  thus False
    using assms(2) non_byzantine_most_recent_for
    by blast
qed

definition (in highway) most_recent :: "'a set \<Rightarrow> 'a set" where
  "most_recent S = \<Union>{ s . \<exists> v. s = most_recent_for v S }"

lemma (in highway) most_recent_idem:
  "most_recent (most_recent S) = most_recent S"
  unfolding most_recent_def most_recent_for_def by auto

lemma (in highway) downset_most_recent_for_subset:
  "\<down> (most_recent S) \<subseteq> \<down> S"
proof (intro subsetI)
  fix x
  assume "x \<in> \<down> (most_recent S)"
  hence "\<exists> y \<in> S . x \<sqsubseteq> y"
    unfolding most_recent_def most_recent_for_def
    by blast
  thus "x \<in> \<down> S" by auto
qed

lemma (in highway) downset_most_recent_for:
  assumes "finite S"
  shows "\<down> (most_recent S) = \<down> S"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> \<down> (most_recent S)"
  thus "x \<in> \<down> S"
    using downset_most_recent_for_subset by blast 
next
  fix x
  assume "x \<in> \<down> S"
  from this obtain v y m where
      "v = sender y"
      "m \<in> most_recent_for v S"
      "x \<sqsubseteq> y"
      "y \<sqsubseteq> m"
    using \<open>finite S\<close> most_recent_exists by fastforce
  hence "x \<in> \<down> (most_recent_for v S)"
    by (metis CollectI leq_trans)
  thus "x \<in> \<down> (most_recent S)"
    unfolding most_recent_def
    by blast
qed

lemma (in highway) most_recent_byzantine_impl:
  "byzantine_in (most_recent S) v \<Longrightarrow> byzantine_in S v"
  unfolding 
    most_recent_def 
    most_recent_for_def 
    byzantine_in_def
    equivocation_def
  by blast

lemma (in highway) most_recent_byzantine_iff:
  assumes "finite S"
  shows "byzantine_in (most_recent S) v = byzantine_in S v"
proof
  assume "byzantine_in (most_recent S) v"
  thus "byzantine_in S v"
    unfolding 
      most_recent_def 
      most_recent_for_def 
      byzantine_in_def
      equivocation_def
    by blast
next
  assume "byzantine_in S v"
  from this obtain x y p q t u where
      "p \<in> S" 
      "q \<in> S"
      "t = sender p"
      "u = sender q"
      "x \<sqsubseteq> p"
      "y \<sqsubseteq> q"
      "v = sender x" 
      "v = sender y"
      "\<not> x \<sqsubseteq> y" 
      "\<not> y \<sqsubseteq> x"
    unfolding byzantine_in_def equivocation_def 
    by blast
  moreover from this obtain m n where
      "p \<sqsubseteq> m"
      "q \<sqsubseteq> n"
      "m \<in> most_recent S"
      "n \<in> most_recent S"
    unfolding most_recent_def
    using 
      most_recent_exists [ OF \<open>finite S\<close> \<open>p \<in> S\<close> \<open>t = sender p\<close> ]
      most_recent_exists [ OF \<open>finite S\<close> \<open>q \<in> S\<close> \<open>u = sender q\<close> ]
    by blast
  ultimately 
  show "byzantine_in (most_recent S) v"
    unfolding byzantine_in_def equivocation_def
    using leq_trans by blast
qed

definition (in highway)
  majority_option :: "'a set \<Rightarrow> 'a vote_option \<Rightarrow> bool" where
  "majority_option S a = 
     (weight\<^sub>\<M> S { s \<in> most_recent S . a = vote_value s } 
     > weight\<^sub>\<M> S { s \<in> most_recent S . a \<noteq> vote_value s })"

lemma (in highway) at_most_one_majority_option:
  assumes "finite S" "majority_option S v" and "majority_option S w"
  shows "v = w"
proof (rule ccontr)
  let ?S' = "most_recent S"
  assume "v \<noteq> w"
  hence
    "{ s \<in> ?S' . v = vote_value s } \<subseteq> { s \<in> ?S' . w \<noteq> vote_value s }"
    (is "?v_votes \<subseteq> ?w_opposing_votes")
    "{ s \<in> ?S' . w = vote_value s } \<subseteq> { s \<in> ?S' . v \<noteq> vote_value s }"
    (is "?w_votes \<subseteq> ?v_opposing_votes")
    by blast+
  moreover have "?S' \<subseteq> S" 
    unfolding most_recent_def most_recent_for_def
    by blast
  hence "finite ?S'"
    using assms(1) infinite_super by auto
  ultimately have
    "weight\<^sub>\<M> S ?v_votes \<le> weight\<^sub>\<M> S ?w_opposing_votes"
    "weight\<^sub>\<M> S ?w_votes \<le> weight\<^sub>\<M> S ?v_opposing_votes"
    by (simp add: messages_weight_mono)+
  hence 
    "weight\<^sub>\<M> S ?v_votes < weight\<^sub>\<M> S ?w_votes"
    "weight\<^sub>\<M> S ?w_votes < weight\<^sub>\<M> S ?v_votes"
    using assms
    unfolding majority_option_def
    by linarith+
  thus False
    by auto
qed

section \<open> Finality \<close>

class highway_summit = highway +
  assumes finite_weight: "finite { v . weight v \<noteq> 0 }"
  assumes finite_citations: "finite (\<down> { m })"
  assumes majority_driven: 
    "majority_option {u . u \<sqsubseteq> m \<and> u \<noteq> m} a \<Longrightarrow> vote_value m = a"

definition (in highway) 
  horizon :: "'a set \<Rightarrow> 'a vote_option \<Rightarrow> 'a set \<Rightarrow> bool" where
  "horizon state a x \<equiv> 
    x \<noteq> {} \<and> x \<subseteq> \<down> state
    \<and> (\<forall> m \<in> x. \<forall> n \<in> \<down> state. 
           sender m = sender n 
           \<longrightarrow> m \<sqsubseteq> n 
           \<longrightarrow> vote_value n = a)"

definition (in highway) validator_weight :: "('a validator) set \<Rightarrow> rat" where
  [simp]: "validator_weight V = (\<Sum> v | v \<in> V \<and> weight v \<noteq> 0 . weight v)"

definition (in highway) committee_weight 
  :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> rat" where
  [simp]: "committee_weight m y x = 
             validator_weight 
                { v. \<exists> u \<in> y. v = sender u 
                      \<and> (\<exists> n \<in> x. v = sender n \<and> n \<sqsubseteq> u \<and> n \<sqsubseteq> m) }"

fun (in highway) summit
   :: "rat \<Rightarrow> 'a set \<Rightarrow> 'a vote_option \<Rightarrow> ('a set) list \<Rightarrow> bool" where
    "summit _ _ _ [] = True"
  | "summit _ state a [x] = horizon state a x"
  | "summit q state a (x # x' # xs) =
       (horizon state a x
           \<and> (\<forall> m \<in> x. q \<le> committee_weight m x x')
           \<and> summit q state a (x' # xs))"

lemma (in highway) summit_left_weaken:
  "summit q state a (xs @ ys) \<Longrightarrow> summit q state a xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof (cases "xs = []")
    case True
    show ?thesis
      by (metis
            True
            Cons.prems 
            append_Cons
            summit.simps(2)
            summit.simps(3) 
            min_list.cases) 
  next
    case False
    from this obtain x' xs' where
      "xs = x' # xs'"
      by (meson neq_Nil_conv)
    then show ?thesis
      using Cons.hyps Cons.prems
      unfolding summit.simps(3) by auto
  qed
qed 

definition (in highway) message_weight :: "'a set \<Rightarrow> rat" where
  [simp]: "message_weight M = validator_weight (image sender M)"


theorem (in highway_summit) elementary_finality:
  assumes 
    "summit (validator_weight UNIV / 2) S a [y,x]"
    "validator_weight { v. byzantine v } = 0"
    "y \<subseteq> \<down> {n}"
  shows "vote_value n = a"
  sorry

(*
theorem (in highway_summit) finality:
  fixes m
  fixes t :: rat
  assumes
    "S \<subseteq> {u . u \<sqsubseteq> m \<and> u \<noteq> m}"
    and "\<forall> v . \<not> byzantine_in S v"
    and "0 < t"
    and "m \<sqsubseteq> n"
    and \<dagger>: "summit (message_weight S / 2 + t) S a xs"
    and \<ddagger>: 
      "validator_weight { v. byzantine v } 
           \<le> 2 * t * (1 - (1 / 2) ^ length xs)" (is "?byz_weight \<le> _")
  shows "vote_value n = a"
  using \<dagger> \<ddagger>
proof (induct xs)
  case Nil
  hence "?byz_weight \<le> t * 3 / 2" sorry
  show ?case
  proof (rule ccontr)
    let ?n_lt = "{u . u \<sqsubseteq> n \<and> u \<noteq> n}"
    let ?not_a_votes = "{s \<in> most_recent ?n_lt. a \<noteq> vote_value s}"
    let ?a_votes = "{s \<in> most_recent ?n_lt. a = vote_value s}"
    assume "vote_value n \<noteq> a"
    hence "weight\<^sub>\<M> ?n_lt ?not_a_votes \<ge> weight\<^sub>\<M> ?n_lt ?not_a_votes" 
      using 
        majority_driven [where m=n and a=a]
        le_less_linear
      unfolding 
        majority_option_def
        honest_message_weight_def
      by blast
    show False sorry
  qed
next
  case (Cons a xs)
  then show ?case sorry
qed
*)

end