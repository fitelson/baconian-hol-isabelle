theory Bacon_PP_ZF_Modal_Word_Normalization
  imports
    Bacon_PP_ZF_Fresh_Higher_Order_Quantified_Fragment_Model
begin

section \<open>Closed unary modal words\<close>

text \<open>
  A modal word records the successive modal operators outside its argument.
  The Boolean parameter records whether the argument is negated.  Thus
  \<open>[PPBox, PPDiamond]\<close> with parameter \<open>False\<close> denotes
  \(\lambda p.\Box\Diamond p\), while the same word with parameter
  \<open>True\<close> denotes \(\lambda p.\Box\Diamond\neg p\).

  This representation is independent of any depth-two fragment model.
  Later normal-form arguments may recurse over arbitrary words.
\<close>

datatype pp_modal_letter = PPBox | PPDiamond

fun pp_modal_body :: "pp_modal_letter list \<Rightarrow> oterm \<Rightarrow> oterm"
where
  "pp_modal_body [] A = A"
| "pp_modal_body (PPBox # ms) A =
    \<box>\<^sub>o (pp_modal_body ms A)"
| "pp_modal_body (PPDiamond # ms) A =
    \<diamond>\<^sub>o (pp_modal_body ms A)"

definition pp_modal_word_term ::
    "pp_modal_letter list \<Rightarrow> bool \<Rightarrow> oterm"
where
  "pp_modal_word_term ms negative =
    Lam Prop
      (pp_modal_body ms
        (if negative then Neg (Var 0) else Var 0))"

lemma typed_pp_modal_body:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> pp_modal_body ms A : Prop"
  using assms
proof (induction ms arbitrary: A)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  then show ?case
    by (cases m)
      (auto intro: typed_ObjBox typed_ObjDiamond)
qed

lemma typed_pp_modal_word_term:
  "[] \<turnstile> pp_modal_word_term ms negative :
    (Prop \<rightarrow>\<^sub>o Prop)"
  unfolding pp_modal_word_term_def
  by (rule has_type.Lam)
    (rule typed_pp_modal_body, cases negative;
      auto intro: has_type.Neg)

lemma pp_modal_body_const_free:
  assumes "consts_of A = {}"
  shows "consts_of (pp_modal_body ms A) = {}"
  using assms
proof (induction ms arbitrary: A)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  then show ?case
    by (cases m)
      (simp_all add: ObjDiamond_def ObjBox_def ObjTrue_def)
qed

lemma pp_modal_word_term_logical:
  "pp_logical_vocabulary (pp_modal_word_term ms negative)"
  unfolding pp_logical_vocabulary_def pp_modal_word_term_def
  by (simp add: pp_modal_body_const_free)

section \<open>Set-theoretic denotation of a modal word\<close>

fun pp_t_modal_word_predicate ::
    "pp_modal_letter list \<Rightarrow>
      bool \<Rightarrow> bool list \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_t_modal_word_predicate [] negative w p =
    (if negative then \<not> pp_t_holds p w else pp_t_holds p w)"
| "pp_t_modal_word_predicate (PPBox # ms) negative w p =
    (\<forall>v. prefix w v \<longrightarrow>
      pp_t_modal_word_predicate ms negative v p)"
| "pp_t_modal_word_predicate (PPDiamond # ms) negative w p =
    (\<exists>v. prefix w v \<and>
      pp_t_modal_word_predicate ms negative v p)"

lemma pp_t_modal_word_predicate_respects:
  assumes x: "Elem x (pp_t_domain Prop)"
    and y: "Elem y (pp_t_domain Prop)"
    and xy: "pp_t_eqv Prop w x y"
    and future: "prefix w v"
  shows "pp_t_modal_word_predicate ms negative v x =
    pp_t_modal_word_predicate ms negative v y"
  using future
proof (induction ms arbitrary: v)
  case Nil
  have at_v:
      "pp_t_holds x v \<longleftrightarrow> pp_t_holds y v"
    using pp_t_prop_eqv_at[OF xy Nil.prems] .
  then show ?case
    by (cases negative) auto
next
  case (Cons m ms)
  show ?case
  proof (cases m)
    case PPBox
    show ?thesis
      unfolding PPBox pp_t_modal_word_predicate.simps
    proof (intro iffI allI impI)
      fix u
      assume all_x:
          "\<forall>u. prefix v u \<longrightarrow>
            pp_t_modal_word_predicate ms negative u x"
        and vu: "prefix v u"
      have wu: "prefix w u"
        using Cons.prems vu prefix_order.trans by blast
      have equal:
          "pp_t_modal_word_predicate ms negative u x =
           pp_t_modal_word_predicate ms negative u y"
        using Cons.IH[OF wu] .
      show "pp_t_modal_word_predicate ms negative u y"
        using all_x vu equal by blast
    next
      fix u
      assume all_y:
          "\<forall>u. prefix v u \<longrightarrow>
            pp_t_modal_word_predicate ms negative u y"
        and vu: "prefix v u"
      have wu: "prefix w u"
        using Cons.prems vu prefix_order.trans by blast
      have equal:
          "pp_t_modal_word_predicate ms negative u x =
           pp_t_modal_word_predicate ms negative u y"
        using Cons.IH[OF wu] .
      show "pp_t_modal_word_predicate ms negative u x"
        using all_y vu equal by blast
    qed
  next
    case PPDiamond
    show ?thesis
      unfolding PPDiamond pp_t_modal_word_predicate.simps
    proof (intro iffI)
      assume "\<exists>u. prefix v u \<and>
        pp_t_modal_word_predicate ms negative u x"
      then obtain u where vu: "prefix v u"
        and at_u: "pp_t_modal_word_predicate ms negative u x"
        by blast
      have wu: "prefix w u"
        using Cons.prems vu prefix_order.trans by blast
      have equal:
          "pp_t_modal_word_predicate ms negative u x =
           pp_t_modal_word_predicate ms negative u y"
        using Cons.IH[OF wu] .
      show "\<exists>u. prefix v u \<and>
        pp_t_modal_word_predicate ms negative u y"
        using vu at_u equal by blast
    next
      assume "\<exists>u. prefix v u \<and>
        pp_t_modal_word_predicate ms negative u y"
      then obtain u where vu: "prefix v u"
        and at_u: "pp_t_modal_word_predicate ms negative u y"
        by blast
      have wu: "prefix w u"
        using Cons.prems vu prefix_order.trans by blast
      have equal:
          "pp_t_modal_word_predicate ms negative u x =
           pp_t_modal_word_predicate ms negative u y"
        using Cons.IH[OF wu] .
      show "\<exists>u. prefix v u \<and>
        pp_t_modal_word_predicate ms negative u x"
        using vu at_u equal by blast
    qed
  qed
qed

lemma pp_t_modal_word_predicate_admissible:
  "pp_t_predicate_admissible Prop
    (pp_t_modal_word_predicate ms negative)"
  unfolding pp_t_predicate_admissible_def
  using pp_t_modal_word_predicate_respects by blast

definition pp_t_modal_word_operator ::
    "pp_modal_letter list \<Rightarrow> bool \<Rightarrow> ZF"
where
  "pp_t_modal_word_operator ms negative =
    pp_t_classifier Prop
      (pp_t_modal_word_predicate ms negative)"

lemma pp_t_modal_word_operator_in_domain:
  "Elem (pp_t_modal_word_operator ms negative)
    (pp_t_domain pp_t_constants_unary_type)"
  unfolding pp_t_modal_word_operator_def
  by (rule pp_t_classifier_in_domain)
    (rule pp_t_modal_word_predicate_admissible)

lemma pp_t_modal_word_operator_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_modal_word_operator ms negative \<acute> p) w
    \<longleftrightarrow>
      pp_t_modal_word_predicate ms negative w p"
  unfolding pp_t_modal_word_operator_def
  using pp_t_classifier_holds[OF p] by simp

lemma pp_t_modal_body_holds:
  assumes env: "pp_t_env_typed [Prop] \<rho>"
    and p: "Elem p (pp_t_domain Prop)"
    and env_zero: "\<rho> 0 = p"
  shows "pp_t_holds
      (pp_t_eval pp_t_default_constants \<rho>
        (pp_modal_body ms
          (if negative then Neg (Var 0) else Var 0))) w
    \<longleftrightarrow>
      pp_t_modal_word_predicate ms negative w p"
  using env p env_zero
proof (induction ms arbitrary: w)
  case Nil
  then show ?case
    by (cases negative) simp_all
next
  case (Cons m ms)
  then show ?case
    by (cases m)
      (auto simp: pp_t_eval_ObjBox_holds
        ObjDiamond_def ObjBox_def ObjTrue_def)
qed

lemma pp_t_modal_word_term_holds:
  assumes p: "Elem p (pp_t_domain Prop)"
  shows "pp_t_holds
      (pp_t_closed_den (pp_modal_word_term ms negative) \<acute> p) w
    \<longleftrightarrow>
      pp_t_modal_word_predicate ms negative w p"
proof -
  have extended:
      "pp_t_env_typed [Prop]
        (extend_env p pp_t_closed_env)"
    using pp_t_env_typed_extend[
      OF pp_t_empty_env_typed p] .
  have body:
      "pp_t_holds
        (pp_t_eval pp_t_default_constants
          (extend_env p pp_t_closed_env)
          (pp_modal_body ms
            (if negative then Neg (Var 0) else Var 0))) w
      \<longleftrightarrow>
        pp_t_modal_word_predicate ms negative w p"
    by (rule pp_t_modal_body_holds[
      OF extended p])
      simp
  show ?thesis
  proof (cases negative)
    case True
    show ?thesis
      unfolding pp_t_closed_den_def pp_modal_word_term_def
      using body True p by (simp add: Lambda_app)
  next
    case False
    show ?thesis
      unfolding pp_t_closed_den_def pp_modal_word_term_def
      using body False p by (simp add: Lambda_app)
  qed
qed

theorem pp_t_modal_word_term_eqv_operator:
  "pp_t_eqv pp_t_constants_unary_type w
    (pp_t_closed_den (pp_modal_word_term ms negative))
    (pp_t_modal_word_operator ms negative)"
proof (rule pp_t_arrow_eqv_if_pointwise)
  show "Elem
      (pp_t_closed_den (pp_modal_word_term ms negative))
      (pp_t_domain pp_t_constants_unary_type)"
    using pp_t_closed_den_in_domain[
      OF typed_pp_modal_word_term] by simp
  show "Elem (pp_t_modal_word_operator ms negative)
      (pp_t_domain pp_t_constants_unary_type)"
    by (rule pp_t_modal_word_operator_in_domain)
  show "\<forall>v. prefix w v \<longrightarrow>
      (\<forall>p. Elem p (pp_t_domain Prop) \<longrightarrow>
        pp_t_eqv Prop v
          (pp_t_closed_den
            (pp_modal_word_term ms negative) \<acute> p)
          (pp_t_modal_word_operator ms negative \<acute> p))"
    unfolding pp_t_eqv.simps
    using pp_t_modal_word_term_holds
      pp_t_modal_word_operator_holds
    by blast
qed

section \<open>Truth values and the first normalization boundary\<close>

lemma pp_t_modal_word_predicate_truth:
  "pp_t_modal_word_predicate ms negative w (pp_zf_truth b)
    \<longleftrightarrow> (if negative then \<not> b else b)"
proof (induction ms arbitrary: w)
  case Nil
  then show ?case by (cases negative) simp_all
next
  case (Cons m ms)
  show ?case
  proof (cases m)
    case PPBox
    show ?thesis
      unfolding PPBox pp_t_modal_word_predicate.simps
      using Cons.IH
      by (cases "if negative then \<not> b else b")
        (auto intro: exI[of _ w])
  next
    case PPDiamond
    show ?thesis
      unfolding PPDiamond pp_t_modal_word_predicate.simps
      using Cons.IH
      by (cases "if negative then \<not> b else b")
        (auto intro: exI[of _ w])
  qed
qed

lemma pp_t_modal_word_operator_truth_eqv:
  "pp_t_eqv Prop w
    (pp_t_modal_word_operator ms negative \<acute> pp_zf_truth b)
    (pp_zf_truth (if negative then \<not> b else b))"
  unfolding pp_t_eqv.simps
  using pp_t_modal_word_operator_holds[
      OF pp_t_truth_in_domain]
    pp_t_modal_word_predicate_truth
  by simp

definition pp_modal_depth_two_alternation ::
    "pp_modal_letter list \<Rightarrow> bool"
where
  "pp_modal_depth_two_alternation ms \<longleftrightarrow>
    ms = [PPBox, PPDiamond] \<or>
    ms = [PPDiamond, PPBox]"

lemma pp_modal_depth_two_alternation_cases:
  assumes "pp_modal_depth_two_alternation ms"
  obtains "ms = [PPBox, PPDiamond]"
    | "ms = [PPDiamond, PPBox]"
  using assms
  unfolding pp_modal_depth_two_alternation_def by blast

text \<open>
  The following syntactic classification isolates the only length-two words
  that are not immediate repetitions.  It is a syntactic classification only:
  the retired depth-two fragment never supplied a semantic repetition theorem.
\<close>

lemma pp_modal_word_length_two_cases:
  assumes "length ms \<le> 2"
  obtains
      "ms = []"
    | "ms = [PPBox]"
    | "ms = [PPDiamond]"
    | "ms = [PPBox, PPBox]"
    | "ms = [PPDiamond, PPDiamond]"
    | "pp_modal_depth_two_alternation ms"
  using assms
  unfolding pp_modal_depth_two_alternation_def
  by (cases ms; cases "tl ms"; cases "hd ms";
      cases "hd (tl ms)"; auto)

end
